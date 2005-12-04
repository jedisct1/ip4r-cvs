/* $Id: ip4r.c,v 1.4 2005-12-04 15:23:59 andrewsn Exp $ */
/*
  New type 'ip4' used to represent a single IPv4 address efficiently

  New type 'ip4r' used to represent a range of IPv4 addresses, along
  with support for GiST and rtree indexing of the type.

  V0.1: updates for 8.1. add some documentation and new functions.
  WARNING: semantics of &<< and &>> changed to track changes in rtree.

  V0.08: SQL changes only; functions returning "internal" must take
  at least one parameter of type "internal".

  V0.07: fix GIST interfaces for 8.0.

  V0.06: make everything 8.0-friendly. For no clear reason the inet
  type renamed some struct elements between 7.4 and 8.0, so the casts
  between ip4 and inet break. Steve Atkins <steve@blighty.com>

  V0.05: mess with operators a bit. clean up error handling. Hopefully,
  this should freeze the visible interface for the forseeable future.

  V0.04: change semantics of &<< and &>> to match rtree requirements

  V0.03: new gist picksplit function based on code from rtree_gist,
  which seems much better than the previous seg-based version. Changed
  the cost metric back so that ip4r_size returns the actual number of
  IPs in the range.

  V0.02: added rtree, changed some cost metrics. The gist code is
  broken somehow; the resulting indexes are bloated with excessive
  numbers of single-value leaf pages.

  this code by andrew@supernews.net Oct 2004 - Dec 2005

  [derived from 'ipr' by:  
   Steve Atkins <steve@blighty.com> August 2003, derived from the 'seg'
   type distributed with PostgreSQL.]

  Distributed under the same terms as PostgreSQL itself.
*/

/******************************************************************************
  This file contains routines that can be bound to a Postgres backend and
  called by the backend in the process of processing queries.  The calling
  format for these routines is dictated by Postgres architecture.
******************************************************************************/

#include <stdio.h>
#include "postgres.h"

#include "access/gist.h"
#include "access/skey.h"
#include "access/hash.h"
#include "libpq/pqformat.h"
#include "utils/elog.h"
#include "utils/palloc.h"
#include "utils/builtins.h"
#include "utils/inet.h"
#include <sys/socket.h>
#include <math.h>

/* IP4 = uint32, stored in host-order. fixed-length and pass by value. */
typedef uint32 IP4;

/* IP4R = range of IP4, stored in host-order. fixed-length by reference */
typedef struct IP4R {
    IP4 lower;
    IP4 upper;
} IP4R;

/**************************************************************************/
/* This part is the internal implementation of all functionality, with no
 * reference to the interface with postgres. That part comes later and is
 * implemented in terms of these functions.
 */

static inline
uint32 hostmask(unsigned masklen)
{
    return (masklen) ? ( (((uint32)(1U)) << (32-masklen)) - 1U ) : 0xFFFFFFFFU;
}

static inline
uint32 netmask(unsigned masklen)
{
    return ~hostmask(masklen);
}

/* if LO and HI are ends of a CIDR prefix, return the mask length.
 * If not, returns ~0.
 */

static inline
unsigned masklen(uint32 lo, uint32 hi)
{
    uint32 d = (lo ^ hi) + 1;
    /* at this point, d can be:
     *  0 if A and B have all bits different
     *  1 if A and B are equal
     *  1 << (32-masklen)
     *  some other value if A and B are not ends of a CIDR range
     * but in any case, after extracting the masklen, we have to
     * recheck because some non-CIDR ranges will produce the same
     * results.
     */
    int fbit = ffs(d);
    switch (fbit)
    {
	case 0: return (lo == 0 && hi == ~0) ? 0 : ~0;
	case 1: return (lo == hi) ? 32 : ~0;
	default:
	    if ( ((uint32)(1U) << (fbit-1)) == d )
	    {
		uint32 mask = hostmask(33-fbit);
		if ((lo & mask) == 0 && (hi & mask) == mask)
		    return 33-fbit;
	    }
	    return ~0;
    }
}

static inline
bool ip4_valid_netmask(uint32 mask)
{
    uint32 d = ~mask + 1;
    /* at this point, d can be:
     *  0 if mask was 0x00000000 (valid)
     *  1 << (32-masklen)   (valid)
     *  some other value  (invalid)
     */
    int fbit = ffs(d);
    switch (fbit)
    {
	case 0:
	    return true;
	default:
	    return ( ((uint32)(1U) << (fbit-1)) == d );
    }
}


/* extract an IP from text. Don't try and use inet_addr/inet_aton, because
 * they often support too many bogus historical formats (octal or hex,
 * classful addresses with less than three dots, etc.)
 */
static inline
bool ip4_from_str(char *str, IP4 *ip)
{
    unsigned a,b,c,d;
    char dummy;
    if (sscanf(str, "%u.%u.%u.%u%c", &a,&b,&c,&d, &dummy) == 4
	&& (a|b|c|d) < 256)
    {
	*ip = (a << 24) | (b << 16) | (c << 8) | d;
	return TRUE;
    }
    return FALSE;
}

/* Output an ip in text form
 */
static inline
int ip4_to_str(IP4 ip, char *str, int slen)
{
    return snprintf(str, slen, "%u.%u.%u.%u",
		    (ip >> 24)&0xff, (ip >> 16)&0xff, (ip >> 8)&0xff, (ip)&0xff);
}

static inline
bool ip4r_from_cidr(IP4 prefix, unsigned masklen, IP4R *ipr)
{
    uint32 mask = hostmask(masklen);
    if (masklen > 32)
	return FALSE;
    if (prefix & mask)
	return FALSE;
    ipr->lower = prefix;
    ipr->upper = prefix | mask;
    return TRUE;
}

static inline
bool ip4r_from_inet(IP4 addr, unsigned masklen, IP4R *ipr)
{
    uint32 mask = hostmask(masklen);
    if (masklen > 32)
	return FALSE;
    ipr->lower = addr & ~mask;
    ipr->upper = addr | mask;
    return TRUE;
}


/* extract an IP range from text.
 */
static
bool ip4r_from_str(char *str, IP4R *ipr)
{
    unsigned a,b,c,d;
    unsigned a2,b2,c2,d2;
    char dummy;
    if (sscanf(str, "%u.%u.%u.%u-%u.%u.%u.%u%c", &a,&b,&c,&d, &a2,&b2,&c2,&d2, &dummy) == 8
	&& (a|b|c|d|a2|b2|c2|d2) < 256)
    {
	IP4 l = (a << 24) | (b << 16) | (c << 8) | d;
	IP4 h = (a2 << 24) | (b2 << 16) | (c2 << 8) | d2;
	if (l > h)
	    ipr->lower = h, ipr->upper = l;
	else
	    ipr->lower = l, ipr->upper = h;
	return TRUE;
    }
    else if (sscanf(str, "%u.%u.%u.%u/%u%c", &a,&b,&c,&d, &a2, &dummy) == 5
	&& (a|b|c|d) < 256 && a2 <= 32)
    {
	IP4 pfx = (a << 24) | (b << 16) | (c << 8) | d;
	return ip4r_from_cidr(pfx, a2, ipr);
    }
    else if (sscanf(str, "%u.%u.%u.%u%c", &a,&b,&c,&d, &dummy) == 4
	&& (a|b|c|d) < 256)
    {
	ipr->lower = ipr->upper = (a << 24) | (b << 16) | (c << 8) | d;
	return TRUE;
    }
    return FALSE;
}

/* Output an ip range in text form
 */
static inline
int ip4r_to_str(IP4R *ipr, char *str, int slen)
{
    IP4 lo = ipr->lower;
    IP4 hi = ipr->upper;
    unsigned msk;
    if (lo == hi)
	return ip4_to_str(lo, str, slen);
    if ((msk = masklen(lo,hi)) <= 32)
	return snprintf(str, slen, "%u.%u.%u.%u/%u",
			(lo >> 24)&0xff, (lo >> 16)&0xff, (lo >> 8)&0xff, (lo)&0xff, msk);
    return snprintf(str, slen, "%u.%u.%u.%u-%u.%u.%u.%u",
		    (lo >> 24)&0xff, (lo >> 16)&0xff, (lo >> 8)&0xff, (lo)&0xff,
		    (hi >> 24)&0xff, (hi >> 16)&0xff, (hi >> 8)&0xff, (hi)&0xff);
}

/* helpers for union/intersection for indexing */

static inline
IP4R *ip4r_union_internal(IP4R *a, IP4R *b, IP4R *result)
{
    if (a->lower < b->lower)
	result->lower = a->lower;
    else
	result->lower = b->lower;

    if (a->upper > b->upper)
	result->upper = a->upper;
    else
	result->upper = b->upper;

    return result;
}

static inline
IP4R *ip4r_inter_internal(IP4R *a, IP4R *b, IP4R *result)
{
    if (a->upper < b->lower || a->lower > b->upper)
    {
	/* disjoint */
	result->lower = 1;
	result->upper = 0;  /* INVALID VALUE */
	return NULL;
    }

    if (a->upper < b->upper)
	result->upper = a->upper;
    else
	result->upper = b->upper;

    if (a->lower > b->lower)
	result->lower = a->lower;
    else
	result->lower = b->lower;

    return result;
}

static inline
double ip4r_metric(IP4R *v)
{
    if (!v)
	return 0.0;
    return ((v->upper - v->lower) + 1.0);
}

/* comparisons */

static inline
bool ip4_equal(IP4 a, IP4 b)
{
    return (a == b);
}

static inline
bool ip4_lessthan(IP4 a, IP4 b)
{
    return (a < b);
}

static inline
bool ip4_less_eq(IP4 a, IP4 b)
{
    return (a <= b);
}

static inline
bool ip4r_equal(IP4R *a, IP4R *b)
{
    return (a->lower == b->lower && a->upper == b->upper);
}

static inline
bool ip4r_lessthan(IP4R *a, IP4R *b)
{
    return (a->lower == b->lower) ? (a->upper < b->upper) : (a->lower < b->lower);
}

static inline
bool ip4r_less_eq(IP4R *a, IP4R *b)
{
    return (a->lower == b->lower) ? (a->upper <= b->upper) : (a->lower < b->lower);
}

static inline
bool ip4r_contains_internal(IP4R *left, IP4R *right, bool eqval)
{
    if (ip4r_equal(left,right))
	return eqval;
    return ((left->lower <= right->lower) && (left->upper >= right->upper));
}

static inline
bool ip4r_overlaps_internal(IP4R *left, IP4R *right)
{
    return (left->upper >= right->lower && left->lower <= right->upper);
}

static inline
bool ip4_contains_internal(IP4R *left, IP4 right)
{
    return (left->lower <= right && left->upper >= right);
}

static inline
bool ip4r_left_internal(IP4R *left, IP4R *right)
{
    return (left->upper < right->lower);
}

static inline
bool ip4r_extends_left_of_internal(IP4R *left, IP4R *right)
{
    return (left->lower < right->lower);
}

static inline
bool ip4r_extends_right_of_internal(IP4R *left, IP4R *right)
{
    return (left->upper > right->upper);
}



/**************************************************************************/
/* This part handles all aspects of postgres interfacing.
 */

#define DatumGetIP4RP(X)	((IP4R *) DatumGetPointer(X))
#define IP4RPGetDatum(X)	PointerGetDatum(X)
#define PG_GETARG_IP4R_P(n) DatumGetIP4RP(PG_GETARG_DATUM(n))
#define PG_RETURN_IP4R_P(x) return IP4RPGetDatum(x)

#define PG_GETARG_IP4(n) PG_GETARG_UINT32(n)
#define PG_RETURN_IP4(x) PG_RETURN_UINT32(x)

#if IP4R_PGVER >= 8000000 && IP4R_PGVER < 9000000
#define INET_IPADDR ipaddr
#define GISTENTRYCOUNT(v) ((v)->n)
#define GISTENTRYVEC(v) ((v)->vector)
#elif IP4R_PGVER >= 7000000 && IP4R_PGVER < 8000000
#define INET_IPADDR ip_addr
typedef bytea GistEntryVector;
#define GISTENTRYCOUNT(v) ( (VARSIZE((v)) - VARHDRSZ) / sizeof(GISTENTRY) )
#define GISTENTRYVEC(v) ((GISTENTRY *) VARDATA(entryvec))
#else
#error "Unknown postgresql version"
#endif

Datum ip4_in(PG_FUNCTION_ARGS);
Datum ip4_out(PG_FUNCTION_ARGS);
Datum ip4_recv(PG_FUNCTION_ARGS);
Datum ip4_send(PG_FUNCTION_ARGS);
Datum ip4hash(PG_FUNCTION_ARGS);
Datum ip4_cast_to_text(PG_FUNCTION_ARGS);
Datum ip4_cast_from_text(PG_FUNCTION_ARGS);
Datum ip4_cast_from_inet(PG_FUNCTION_ARGS);
Datum ip4_cast_to_cidr(PG_FUNCTION_ARGS);
Datum ip4_cast_to_bigint(PG_FUNCTION_ARGS);
Datum ip4_cast_from_bigint(PG_FUNCTION_ARGS);
Datum ip4_cast_to_double(PG_FUNCTION_ARGS);
Datum ip4_cast_from_double(PG_FUNCTION_ARGS);
Datum ip4r_in(PG_FUNCTION_ARGS);
Datum ip4r_out(PG_FUNCTION_ARGS);
Datum ip4r_recv(PG_FUNCTION_ARGS);
Datum ip4r_send(PG_FUNCTION_ARGS);
Datum ip4rhash(PG_FUNCTION_ARGS);
Datum ip4r_cast_to_text(PG_FUNCTION_ARGS);
Datum ip4r_cast_from_text(PG_FUNCTION_ARGS);
Datum ip4r_cast_from_cidr(PG_FUNCTION_ARGS);
Datum ip4r_cast_to_cidr(PG_FUNCTION_ARGS);
Datum ip4r_cast_from_ip4(PG_FUNCTION_ARGS);
Datum ip4r_from_ip4s(PG_FUNCTION_ARGS);
Datum ip4r_net_prefix(PG_FUNCTION_ARGS);
Datum ip4r_net_mask(PG_FUNCTION_ARGS);
Datum ip4r_lower(PG_FUNCTION_ARGS);
Datum ip4r_upper(PG_FUNCTION_ARGS);
Datum ip4r_is_cidr(PG_FUNCTION_ARGS);
Datum ip4_netmask(PG_FUNCTION_ARGS);
Datum ip4_net_lower(PG_FUNCTION_ARGS);
Datum ip4_net_upper(PG_FUNCTION_ARGS);
Datum ip4_plus_int(PG_FUNCTION_ARGS);
Datum ip4_plus_bigint(PG_FUNCTION_ARGS);
Datum ip4_minus_int(PG_FUNCTION_ARGS);
Datum ip4_minus_bigint(PG_FUNCTION_ARGS);
Datum ip4_minus_ip4(PG_FUNCTION_ARGS);
Datum ip4_and(PG_FUNCTION_ARGS);
Datum ip4_or(PG_FUNCTION_ARGS);
Datum ip4_xor(PG_FUNCTION_ARGS);
Datum ip4_not(PG_FUNCTION_ARGS);
Datum ip4_lt(PG_FUNCTION_ARGS);
Datum ip4_le(PG_FUNCTION_ARGS);
Datum ip4_gt(PG_FUNCTION_ARGS);
Datum ip4_ge(PG_FUNCTION_ARGS);
Datum ip4_eq(PG_FUNCTION_ARGS);
Datum ip4_neq(PG_FUNCTION_ARGS);
Datum ip4r_lt(PG_FUNCTION_ARGS);
Datum ip4r_le(PG_FUNCTION_ARGS);
Datum ip4r_gt(PG_FUNCTION_ARGS);
Datum ip4r_ge(PG_FUNCTION_ARGS);
Datum ip4r_eq(PG_FUNCTION_ARGS);
Datum ip4r_neq(PG_FUNCTION_ARGS);
Datum ip4r_overlaps(PG_FUNCTION_ARGS);
Datum ip4r_contains(PG_FUNCTION_ARGS);
Datum ip4r_contains_strict(PG_FUNCTION_ARGS);
Datum ip4r_contained_by(PG_FUNCTION_ARGS);
Datum ip4r_contained_by_strict(PG_FUNCTION_ARGS);
Datum ip4_contains(PG_FUNCTION_ARGS);
Datum ip4_contained_by(PG_FUNCTION_ARGS);
Datum ip4r_union(PG_FUNCTION_ARGS);
Datum ip4r_inter(PG_FUNCTION_ARGS);
Datum ip4r_size(PG_FUNCTION_ARGS);
Datum ip4r_cmp(PG_FUNCTION_ARGS);
Datum ip4_cmp(PG_FUNCTION_ARGS);
Datum ip4r_left_of(PG_FUNCTION_ARGS);
Datum ip4r_left_overlap(PG_FUNCTION_ARGS);
Datum ip4r_right_of(PG_FUNCTION_ARGS);
Datum ip4r_right_overlap(PG_FUNCTION_ARGS);

/*
#define GIST_DEBUG
#define GIST_QUERY_DEBUG
*/

static
text *
make_text(char *str, int len)
{
    text *ret = (text *) palloc(len + VARHDRSZ);
    VARATT_SIZEP(ret) = len + VARHDRSZ;
    if (str)
	memcpy(VARDATA(ret), str, len);
    else
	memset(VARDATA(ret), 0, len);
    return ret;
}

static inline
void
set_text_len(text *txt, int len)
{
    if ((len + VARHDRSZ) < VARATT_SIZEP(txt))
	VARATT_SIZEP(txt) = len + VARHDRSZ;
}

static inline
int
get_text_len(text *txt)
{
    return VARSIZE(txt) - VARHDRSZ;
}

/*
** Input/Output routines
*/

PG_FUNCTION_INFO_V1(ip4_in);
Datum
ip4_in(PG_FUNCTION_ARGS)
{
    char *str = PG_GETARG_CSTRING(0);
    IP4 ip;
    if (ip4_from_str(str, &ip))
	PG_RETURN_IP4(ip);

    ereport(ERROR,
	    (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
	     errmsg("invalid IP4 value: '%s'", str)));
    PG_RETURN_NULL();
}

PG_FUNCTION_INFO_V1(ip4_out);
Datum
ip4_out(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    char *out = palloc(32);
    ip4_to_str(ip, out, 32);
    PG_RETURN_CSTRING(out);
}

PG_FUNCTION_INFO_V1(ip4_recv);
Datum
ip4_recv(PG_FUNCTION_ARGS)
{
    StringInfo buf = (StringInfo) PG_GETARG_POINTER(0);
    PG_RETURN_IP4((IP4) pq_getmsgint(buf, sizeof(IP4)));
}

PG_FUNCTION_INFO_V1(ip4_send);
Datum
ip4_send(PG_FUNCTION_ARGS)
{
    IP4 arg1 = PG_GETARG_IP4(0);
    StringInfoData buf;

    pq_begintypsend(&buf);
    pq_sendint(&buf, arg1, sizeof(IP4));
    PG_RETURN_BYTEA_P(pq_endtypsend(&buf));
}

PG_FUNCTION_INFO_V1(ip4hash);
Datum
ip4hash(PG_FUNCTION_ARGS)
{
    IP4 arg1 = PG_GETARG_IP4(0);

    return hash_any((unsigned char *)&arg1, sizeof(IP4));
}

PG_FUNCTION_INFO_V1(ip4_cast_to_text);
Datum
ip4_cast_to_text(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    text *out = make_text(NULL,32);
    set_text_len(out, ip4_to_str(ip, VARDATA(out), 32));
    PG_RETURN_TEXT_P(out);
}

PG_FUNCTION_INFO_V1(ip4_cast_from_text);
Datum
ip4_cast_from_text(PG_FUNCTION_ARGS)
{
    text *txt = PG_GETARG_TEXT_P(0);
    int tlen = get_text_len(txt);
    char buf[32];

    if (tlen < sizeof(buf))
    {
	IP4 ip;

	memcpy(buf, VARDATA(txt), tlen);
	buf[tlen] = 0;
	if (ip4_from_str(buf, &ip))
	    PG_RETURN_IP4(ip);
    }

    ereport(ERROR,
	    (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
	     errmsg("invalid IP4 value in text")));
    PG_RETURN_NULL();
}

PG_FUNCTION_INFO_V1(ip4_cast_from_inet);
Datum
ip4_cast_from_inet(PG_FUNCTION_ARGS)
{
    inet *inetptr = PG_GETARG_INET_P(0);
    inet_struct *in = ((inet_struct *)VARDATA(inetptr));

    if (in->family == PGSQL_AF_INET)
    {
        unsigned char *p = in->INET_IPADDR;
    	IP4 ip = (p[0] << 24)|(p[1] << 16)|(p[2] << 8)|p[3];
	PG_RETURN_IP4(ip);
    }

    ereport(ERROR,
	    (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
	     errmsg("invalid INET value for conversion to IP4")));
    PG_RETURN_NULL();
}

PG_FUNCTION_INFO_V1(ip4_cast_to_cidr);
Datum
ip4_cast_to_cidr(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    inet *res = palloc0(VARHDRSZ + sizeof(inet_struct));
    inet_struct *in;

    VARATT_SIZEP(res) = VARHDRSZ + offsetof(inet_struct, INET_IPADDR) + 4;

    in = ((inet_struct *)VARDATA(res));
    in->bits = 32;
    in->type = 1;  /* cidr, not inet */
    in->family = PGSQL_AF_INET;
    {
	unsigned char *p = in->INET_IPADDR;
	p[0] = (ip >> 24) & 0xff;
	p[1] = (ip >> 16) & 0xff;
	p[2] = (ip >>  8) & 0xff;
	p[3] = (ip      ) & 0xff;
    }

    PG_RETURN_INET_P(res);
}

PG_FUNCTION_INFO_V1(ip4_cast_to_bigint);
Datum
ip4_cast_to_bigint(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    PG_RETURN_INT64(ip);
}

PG_FUNCTION_INFO_V1(ip4_cast_from_bigint);
Datum
ip4_cast_from_bigint(PG_FUNCTION_ARGS)
{
    int64 val = PG_GETARG_INT64(0);
    PG_RETURN_IP4(val);
}

PG_FUNCTION_INFO_V1(ip4_cast_to_double);
Datum
ip4_cast_to_double(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    PG_RETURN_FLOAT8(ip);
}

PG_FUNCTION_INFO_V1(ip4_cast_from_double);
Datum
ip4_cast_from_double(PG_FUNCTION_ARGS)
{
    float8 val = PG_GETARG_FLOAT8(0);
    float8 ival = 0;

    if (modf(val,&ival) != 0.0)
    {
	ereport(WARNING,
		(errcode(ERRCODE_WARNING),
		 errmsg("double converted to IP4 is not integral")));
    }

    PG_RETURN_IP4((unsigned long) ival);
}

PG_FUNCTION_INFO_V1(ip4_netmask);
Datum
ip4_netmask(PG_FUNCTION_ARGS)
{
    int pfxlen = PG_GETARG_INT32(0);

    if (pfxlen < 0 || pfxlen > 32)
    {
	ereport(ERROR,
		(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
		 errmsg("prefix length out of range")));
    }

    PG_RETURN_IP4( netmask(pfxlen) );
}

PG_FUNCTION_INFO_V1(ip4_net_lower);
Datum
ip4_net_lower(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    int pfxlen = PG_GETARG_INT32(1);

    if (pfxlen < 0 || pfxlen > 32)
    {
	ereport(ERROR,
		(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
		 errmsg("prefix length out of range")));
    }

    PG_RETURN_IP4( ip & netmask(pfxlen) );
}

PG_FUNCTION_INFO_V1(ip4_net_upper);
Datum
ip4_net_upper(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    int pfxlen = PG_GETARG_INT32(1);

    if (pfxlen < 0 || pfxlen > 32)
    {
	ereport(ERROR,
		(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
		 errmsg("prefix length out of range")));
    }

    PG_RETURN_IP4( ip | hostmask(pfxlen) );
}

PG_FUNCTION_INFO_V1(ip4_plus_int);
Datum
ip4_plus_int(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    int addend = PG_GETARG_INT32(1);
    IP4 result = ip + (IP4) addend;

    if ((addend < 0) != (result < ip))
    {
	ereport(ERROR,
		(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
		 errmsg("ip address out of range")));
    }

    PG_RETURN_IP4(result);
}

PG_FUNCTION_INFO_V1(ip4_plus_bigint);
Datum
ip4_plus_bigint(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    int64 addend = PG_GETARG_INT64(1);
    int64 result = (int64) ip + addend;

    if (((addend < 0) != (result < ip))
	|| result != (int64)(IP4)result)
    {
	ereport(ERROR,
		(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
		 errmsg("ip address out of range")));
    }

    PG_RETURN_IP4( (IP4)(result) );
}

PG_FUNCTION_INFO_V1(ip4_minus_int);
Datum
ip4_minus_int(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    int subtrahend = PG_GETARG_INT32(1);
    IP4 result = ip - (IP4) subtrahend;

    if ((subtrahend > 0) != (result < ip))
    {
	ereport(ERROR,
		(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
		 errmsg("ip address out of range")));
    }

    PG_RETURN_IP4(result);
}

PG_FUNCTION_INFO_V1(ip4_minus_bigint);
Datum
ip4_minus_bigint(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    int64 subtrahend = PG_GETARG_INT64(1);
    int64 result = (int64) ip - subtrahend;

    if (((subtrahend > 0) != (result < ip))
	|| result != (int64)(IP4)result)
    {
	ereport(ERROR,
		(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
		 errmsg("ip address out of range")));
    }

    PG_RETURN_IP4( (IP4)(result) );
}

PG_FUNCTION_INFO_V1(ip4_minus_ip4);
Datum
ip4_minus_ip4(PG_FUNCTION_ARGS)
{
    IP4 minuend = PG_GETARG_IP4(0);
    IP4 subtrahend = PG_GETARG_IP4(1);
    int64 result = (int64) minuend - (int64) subtrahend;

    PG_RETURN_INT64(result);
}

PG_FUNCTION_INFO_V1(ip4_and);
Datum
ip4_and(PG_FUNCTION_ARGS)
{
    IP4 a = PG_GETARG_IP4(0);
    IP4 b = PG_GETARG_IP4(1);

    PG_RETURN_IP4(a & b);
}

PG_FUNCTION_INFO_V1(ip4_or);
Datum
ip4_or(PG_FUNCTION_ARGS)
{
    IP4 a = PG_GETARG_IP4(0);
    IP4 b = PG_GETARG_IP4(1);

    PG_RETURN_IP4(a | b);
}

PG_FUNCTION_INFO_V1(ip4_xor);
Datum
ip4_xor(PG_FUNCTION_ARGS)
{
    IP4 a = PG_GETARG_IP4(0);
    IP4 b = PG_GETARG_IP4(1);

    PG_RETURN_IP4(a ^ b);
}

PG_FUNCTION_INFO_V1(ip4_not);
Datum
ip4_not(PG_FUNCTION_ARGS)
{
    IP4 a = PG_GETARG_IP4(0);

    PG_RETURN_IP4(~a);
}


/*---- ip4r ----*/

PG_FUNCTION_INFO_V1(ip4r_in);
Datum
ip4r_in(PG_FUNCTION_ARGS)
{
    char *str = PG_GETARG_CSTRING(0);
    IP4R ipr;
    if (ip4r_from_str(str, &ipr))
    {
	IP4R *res = palloc(sizeof(IP4R));
	*res = ipr;
	PG_RETURN_IP4R_P(res);
    }

    ereport(ERROR,
	    (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
	     errmsg("invalid IP4R value: \"%s\"", str)));
    PG_RETURN_NULL();
}

PG_FUNCTION_INFO_V1(ip4r_out);
Datum
ip4r_out(PG_FUNCTION_ARGS)
{
    IP4R *ipr = PG_GETARG_IP4R_P(0);
    char *out = palloc(32);
    ip4r_to_str(ipr, out, 32);
    PG_RETURN_CSTRING(out);
}

PG_FUNCTION_INFO_V1(ip4r_recv);
Datum
ip4r_recv(PG_FUNCTION_ARGS)
{
    StringInfo buf = (StringInfo) PG_GETARG_POINTER(0);
    IP4R *ipr = palloc(sizeof(IP4R));

    ipr->lower = (IP4) pq_getmsgint(buf, sizeof(IP4));
    ipr->upper = (IP4) pq_getmsgint(buf, sizeof(IP4));

    PG_RETURN_IP4R_P(ipr);
}

PG_FUNCTION_INFO_V1(ip4r_send);
Datum
ip4r_send(PG_FUNCTION_ARGS)
{
    IP4R *ipr = PG_GETARG_IP4R_P(0);
    StringInfoData buf;

    pq_begintypsend(&buf);
    pq_sendint(&buf, ipr->lower, sizeof(IP4));
    pq_sendint(&buf, ipr->upper, sizeof(IP4));
    PG_RETURN_BYTEA_P(pq_endtypsend(&buf));
}

PG_FUNCTION_INFO_V1(ip4rhash);
Datum
ip4rhash(PG_FUNCTION_ARGS)
{
    IP4R *arg1 = PG_GETARG_IP4R_P(0);

    return hash_any((unsigned char *)arg1, sizeof(IP4R));
}

PG_FUNCTION_INFO_V1(ip4r_cast_to_text);
Datum
ip4r_cast_to_text(PG_FUNCTION_ARGS)
{
    IP4R *ipr = PG_GETARG_IP4R_P(0);
    text *out = make_text(NULL,32);
    set_text_len(out, ip4r_to_str(ipr, VARDATA(out), 32));
    PG_RETURN_TEXT_P(out);
}

PG_FUNCTION_INFO_V1(ip4r_cast_from_text);
Datum
ip4r_cast_from_text(PG_FUNCTION_ARGS)
{
    text *txt = PG_GETARG_TEXT_P(0);
    int tlen = get_text_len(txt);
    char buf[32];

    if (tlen < sizeof(buf))
    {
	IP4R ipr;

	memcpy(buf, VARDATA(txt), tlen);
	buf[tlen] = 0;
	if (ip4r_from_str(buf, &ipr))
	{
	    IP4R *res = palloc(sizeof(IP4R));
	    *res = ipr;
	    PG_RETURN_IP4R_P(res);
	}
    }

    ereport(ERROR,
	    (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
	     errmsg("invalid IP4R value in text")));
    PG_RETURN_NULL();
}

PG_FUNCTION_INFO_V1(ip4r_cast_from_cidr);
Datum
ip4r_cast_from_cidr(PG_FUNCTION_ARGS)
{
    inet *inetptr = PG_GETARG_INET_P(0);
    inet_struct *in = ((inet_struct *)VARDATA(inetptr));

    if (in->type && in->family == PGSQL_AF_INET)
    {
        unsigned char *p = in->INET_IPADDR;
    	IP4 ip = (p[0] << 24)|(p[1] << 16)|(p[2] << 8)|p[3];
	IP4R ipr;
	if (ip4r_from_cidr(ip, in->bits, &ipr))
	{
	    IP4R *res = palloc(sizeof(IP4R));
	    *res = ipr;
	    PG_RETURN_IP4R_P(res);
	}
    }

    ereport(ERROR,
	    (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
	     errmsg("invalid CIDR value for conversion to IP4R")));
    PG_RETURN_NULL();
}

PG_FUNCTION_INFO_V1(ip4r_cast_to_cidr);
Datum
ip4r_cast_to_cidr(PG_FUNCTION_ARGS)
{
    IP4R *ipr = PG_GETARG_IP4R_P(0);
    IP4 ip = ipr->lower;
    inet *res;
    inet_struct *in;
    unsigned bits = masklen(ip, ipr->upper);

    if (bits > 32)
	PG_RETURN_NULL();

    res = palloc0(VARHDRSZ + sizeof(inet_struct));
    VARATT_SIZEP(res) = VARHDRSZ + offsetof(inet_struct, INET_IPADDR) + 4;

    in = ((inet_struct *)VARDATA(res));
    in->bits = bits;
    in->type = 1;  /* cidr, not inet */
    in->family = PGSQL_AF_INET;
    {
	unsigned char *p = in->INET_IPADDR;
	p[0] = (ip >> 24) & 0xff;
	p[1] = (ip >> 16) & 0xff;
	p[2] = (ip >>  8) & 0xff;
	p[3] = (ip      ) & 0xff;
    }

    PG_RETURN_INET_P(res);
}

PG_FUNCTION_INFO_V1(ip4r_cast_from_ip4);
Datum
ip4r_cast_from_ip4(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    IP4R *res = palloc(sizeof(IP4R));
    if (ip4r_from_inet(ip, 32, res))
    {
	PG_RETURN_IP4R_P(res);
    }

    pfree(res);
    ereport(ERROR,
	    (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
	     errmsg("invalid IP4 value for conversion to IP4R (shouldn't be possible)")));
    PG_RETURN_NULL();
}

PG_FUNCTION_INFO_V1(ip4r_from_ip4s);
Datum
ip4r_from_ip4s(PG_FUNCTION_ARGS)
{
    IP4 a = PG_GETARG_IP4(0);
    IP4 b = PG_GETARG_IP4(1);
    IP4R *res = palloc(sizeof(IP4R));
    if (a < b)
	res->lower = a, res->upper = b;
    else
	res->lower = b, res->upper = a;
    PG_RETURN_IP4R_P( res );
}

PG_FUNCTION_INFO_V1(ip4r_net_prefix);
Datum
ip4r_net_prefix(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    int pfxlen = PG_GETARG_INT32(1);

    if (pfxlen < 0 || pfxlen > 32)
    {
	ereport(ERROR,
		(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
		 errmsg("prefix length out of range")));
    }

    {
	IP4 mask = netmask(pfxlen);
	IP4R *res = palloc(sizeof(IP4R));
    
	res->lower = ip & mask;
	res->upper = ip | ~mask;

	PG_RETURN_IP4R_P(res);
    }
}

PG_FUNCTION_INFO_V1(ip4r_net_mask);
Datum
ip4r_net_mask(PG_FUNCTION_ARGS)
{
    IP4 ip = PG_GETARG_IP4(0);
    IP4 mask = PG_GETARG_IP4(1);

    if (!ip4_valid_netmask(mask))
    {
	ereport(ERROR,
		(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
		 errmsg("invalid netmask")));
    }

    {
	IP4R *res = palloc(sizeof(IP4R));
    
	res->lower = ip & mask;
	res->upper = ip | ~mask;

	PG_RETURN_IP4R_P(res);
    }
}


PG_FUNCTION_INFO_V1(ip4r_lower);
Datum
ip4r_lower(PG_FUNCTION_ARGS)
{
    IP4R *ipr = PG_GETARG_IP4R_P(0);
    PG_RETURN_IP4( ipr->lower );
}

PG_FUNCTION_INFO_V1(ip4r_upper);
Datum
ip4r_upper(PG_FUNCTION_ARGS)
{
    IP4R *ipr = PG_GETARG_IP4R_P(0);
    PG_RETURN_IP4( ipr->upper );
}

PG_FUNCTION_INFO_V1(ip4r_is_cidr);
Datum
ip4r_is_cidr(PG_FUNCTION_ARGS)
{
    IP4R *ipr = PG_GETARG_IP4R_P(0);
    PG_RETURN_BOOL( (masklen(ipr->lower,ipr->upper) <= 32U) );
}

PG_FUNCTION_INFO_V1(ip4_lt);
Datum
ip4_lt(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4_lessthan(PG_GETARG_IP4(0), PG_GETARG_IP4(1)) );
}

PG_FUNCTION_INFO_V1(ip4_le);
Datum
ip4_le(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4_less_eq(PG_GETARG_IP4(0), PG_GETARG_IP4(1)) );
}

PG_FUNCTION_INFO_V1(ip4_gt);
Datum
ip4_gt(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4_lessthan(PG_GETARG_IP4(1), PG_GETARG_IP4(0)) );
}

PG_FUNCTION_INFO_V1(ip4_ge);
Datum
ip4_ge(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4_less_eq(PG_GETARG_IP4(1), PG_GETARG_IP4(0)) );
}

PG_FUNCTION_INFO_V1(ip4_eq);
Datum
ip4_eq(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4_equal(PG_GETARG_IP4(0), PG_GETARG_IP4(1)) );
}

PG_FUNCTION_INFO_V1(ip4_neq);
Datum
ip4_neq(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( !ip4_equal(PG_GETARG_IP4(0), PG_GETARG_IP4(1)) );
}

PG_FUNCTION_INFO_V1(ip4r_lt);
Datum
ip4r_lt(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_lessthan(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1)) );
}

PG_FUNCTION_INFO_V1(ip4r_le);
Datum
ip4r_le(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_less_eq(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1)) );
}

PG_FUNCTION_INFO_V1(ip4r_gt);
Datum
ip4r_gt(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_lessthan(PG_GETARG_IP4R_P(1), PG_GETARG_IP4R_P(0)) );
}

PG_FUNCTION_INFO_V1(ip4r_ge);
Datum
ip4r_ge(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_less_eq(PG_GETARG_IP4R_P(1), PG_GETARG_IP4R_P(0)) );
}

PG_FUNCTION_INFO_V1(ip4r_eq);
Datum
ip4r_eq(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_equal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1)) );
}

PG_FUNCTION_INFO_V1(ip4r_neq);
Datum
ip4r_neq(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( !ip4r_equal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1)) );
}

PG_FUNCTION_INFO_V1(ip4r_overlaps);
Datum
ip4r_overlaps(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_overlaps_internal(PG_GETARG_IP4R_P(0), 
					   PG_GETARG_IP4R_P(1)) );
}

PG_FUNCTION_INFO_V1(ip4r_contains);
Datum
ip4r_contains(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_contains_internal(PG_GETARG_IP4R_P(0),
					   PG_GETARG_IP4R_P(1),
					   TRUE) );
}

PG_FUNCTION_INFO_V1(ip4r_contains_strict);
Datum
ip4r_contains_strict(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_contains_internal(PG_GETARG_IP4R_P(0),
					   PG_GETARG_IP4R_P(1),
					   FALSE) );
}

PG_FUNCTION_INFO_V1(ip4r_contained_by);
Datum
ip4r_contained_by(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_contains_internal(PG_GETARG_IP4R_P(1),
					   PG_GETARG_IP4R_P(0),
					   TRUE) );
}

PG_FUNCTION_INFO_V1(ip4r_contained_by_strict);
Datum
ip4r_contained_by_strict(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_contains_internal(PG_GETARG_IP4R_P(1),
					   PG_GETARG_IP4R_P(0),
					   FALSE) );
}

PG_FUNCTION_INFO_V1(ip4_contains);
Datum
ip4_contains(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4_contains_internal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4(1)) );
}

PG_FUNCTION_INFO_V1(ip4_contained_by);
Datum
ip4_contained_by(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4_contains_internal(PG_GETARG_IP4R_P(1), PG_GETARG_IP4(0)) );
}

PG_FUNCTION_INFO_V1(ip4r_left_of);
Datum
ip4r_left_of(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_left_internal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1)) );
}

PG_FUNCTION_INFO_V1(ip4r_left_overlap);
Datum 
ip4r_left_overlap(PG_FUNCTION_ARGS)
{
#if IP4R_PGVER < 8001000
    PG_RETURN_BOOL( ip4r_extends_left_of_internal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1)) );
#else
    PG_RETURN_BOOL(! ip4r_extends_right_of_internal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1)) );
#endif
}

PG_FUNCTION_INFO_V1(ip4r_right_of);
Datum
ip4r_right_of(PG_FUNCTION_ARGS)
{
    PG_RETURN_BOOL( ip4r_left_internal(PG_GETARG_IP4R_P(1), PG_GETARG_IP4R_P(0)) );
}

PG_FUNCTION_INFO_V1(ip4r_right_overlap);
Datum
ip4r_right_overlap(PG_FUNCTION_ARGS)
{
#if IP4R_PGVER < 8001000
    PG_RETURN_BOOL( ip4r_extends_right_of_internal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1)) );
#else
    PG_RETURN_BOOL(! ip4r_extends_left_of_internal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1)) );
#endif
}


PG_FUNCTION_INFO_V1(ip4r_union);
Datum
ip4r_union(PG_FUNCTION_ARGS)
{
    IP4R *res = (IP4R *) palloc(sizeof(IP4R));
    ip4r_union_internal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1), res);
    PG_RETURN_IP4R_P(res);
}

PG_FUNCTION_INFO_V1(ip4r_inter);
Datum
ip4r_inter(PG_FUNCTION_ARGS)
{
    IP4R *res = (IP4R *) palloc(sizeof(IP4R));
    if (ip4r_inter_internal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1), res))
    {
	PG_RETURN_IP4R_P(res);
    }
    pfree(res);
    PG_RETURN_NULL();
}

PG_FUNCTION_INFO_V1(ip4r_size);
Datum
ip4r_size(PG_FUNCTION_ARGS)
{
    double size = ip4r_metric(PG_GETARG_IP4R_P(0));
    PG_RETURN_FLOAT8(size);
}


/*****************************************************************************
 *						   Btree functions
 *****************************************************************************/

PG_FUNCTION_INFO_V1(ip4r_cmp);
Datum
ip4r_cmp(PG_FUNCTION_ARGS)
{
    IP4R *a = PG_GETARG_IP4R_P(0);
    IP4R *b = PG_GETARG_IP4R_P(1);
    if (ip4r_lessthan(a,b))
	PG_RETURN_INT32(-1);
    if (ip4r_equal(a,b))
	PG_RETURN_INT32(0);
    PG_RETURN_INT32(1);
}

PG_FUNCTION_INFO_V1(ip4_cmp);
Datum
ip4_cmp(PG_FUNCTION_ARGS)
{
    IP4 a = PG_GETARG_IP4(0);
    IP4 b = PG_GETARG_IP4(1);
    if (ip4_lessthan(a,b))
	PG_RETURN_INT32(-1);
    if (ip4_equal(a,b))
	PG_RETURN_INT32(0);
    PG_RETURN_INT32(1);
}


/*****************************************************************************
 *						   Rtree functions
 *****************************************************************************/

Datum rt_ip4r_union(PG_FUNCTION_ARGS);
Datum rt_ip4r_inter(PG_FUNCTION_ARGS);
Datum rt_ip4r_size(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(rt_ip4r_union);
Datum
rt_ip4r_union(PG_FUNCTION_ARGS)
{
    IP4R *res = (IP4R *) palloc(sizeof(IP4R));
    ip4r_union_internal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1), res);
    PG_RETURN_IP4R_P(res);
}

PG_FUNCTION_INFO_V1(rt_ip4r_inter);
Datum
rt_ip4r_inter(PG_FUNCTION_ARGS)
{
    IP4R *res = (IP4R *) palloc(sizeof(IP4R));
    if (ip4r_inter_internal(PG_GETARG_IP4R_P(0), PG_GETARG_IP4R_P(1), res))
    {
	PG_RETURN_IP4R_P(res);
    }
    pfree(res);
    PG_RETURN_IP4R_P(NULL);
}

PG_FUNCTION_INFO_V1(rt_ip4r_size);
Datum
rt_ip4r_size(PG_FUNCTION_ARGS)
{
    float *psize = (float *) PG_GETARG_POINTER(1);
    *psize = (float) ip4r_metric(PG_GETARG_IP4R_P(0));

    PG_RETURN_VOID();
}

/*****************************************************************************
 *						   GiST functions
 *****************************************************************************/

/*
** GiST support methods
*/

Datum gip4r_consistent(PG_FUNCTION_ARGS);
Datum gip4r_compress(PG_FUNCTION_ARGS);
Datum gip4r_decompress(PG_FUNCTION_ARGS);
Datum gip4r_penalty(PG_FUNCTION_ARGS);
Datum gip4r_picksplit(PG_FUNCTION_ARGS);
Datum gip4r_union(PG_FUNCTION_ARGS);
Datum gip4r_same(PG_FUNCTION_ARGS);

static bool gip4r_leaf_consistent(IP4R * key, IP4R * query, StrategyNumber strategy);
static bool gip4r_internal_consistent(IP4R * key, IP4R * query, StrategyNumber strategy);

/*
** The GiST Consistent method for IP ranges
** Should return false if for all data items x below entry,
** the predicate x op query == FALSE, where op is the oper
** corresponding to strategy in the pg_amop table.
*/
PG_FUNCTION_INFO_V1(gip4r_consistent);
Datum
gip4r_consistent(PG_FUNCTION_ARGS)
{
    GISTENTRY *entry = (GISTENTRY *) PG_GETARG_POINTER(0);
    IP4R *query = (IP4R *) PG_GETARG_POINTER(1);
    StrategyNumber strategy = (StrategyNumber) PG_GETARG_UINT16(2);
    IP4R *key = (IP4R *) DatumGetPointer(entry->key);
    bool retval;

    /*
     * * if entry is not leaf, use gip4r_internal_consistent, * else use
     * gip4r_leaf_consistent
     */
    if (GIST_LEAF(entry))
	retval = gip4r_leaf_consistent(key, query, strategy);
    else
	retval = gip4r_internal_consistent(key, query, strategy);

    PG_RETURN_BOOL(retval);
}

/*
** The GiST Union method for IP ranges
** returns the minimal bounding IP4R that encloses all the entries in entryvec
*/
PG_FUNCTION_INFO_V1(gip4r_union);
Datum
gip4r_union(PG_FUNCTION_ARGS)
{
    GistEntryVector *entryvec = (GistEntryVector *) PG_GETARG_POINTER(0);
    int	*sizep = (int *) PG_GETARG_POINTER(1);
    GISTENTRY *ent = GISTENTRYVEC(entryvec);

    int	numranges, i;
    IP4R *out = (IP4R *) palloc(sizeof(IP4R));
    IP4R *tmp;
  
#ifdef GIST_DEBUG
    fprintf(stderr, "union\n");
#endif
  
    numranges = GISTENTRYCOUNT(entryvec);
    tmp = (IP4R *) DatumGetPointer(ent[0].key);
    *sizep = sizeof(IP4R);
    *out = *tmp;
  
    for (i = 1; i < numranges; i++)
    {
	tmp = (IP4R *) DatumGetPointer(ent[i].key);
	if (tmp->lower < out->lower)
	    out->lower = tmp->lower;
	if (tmp->upper > out->upper)
	    out->upper = tmp->upper;
    }
    
    PG_RETURN_IP4R_P(out);
}

/*
** GiST Compress and Decompress methods for IP ranges
** do not do anything.
*/
PG_FUNCTION_INFO_V1(gip4r_compress);
Datum
gip4r_compress(PG_FUNCTION_ARGS)
{
    PG_RETURN_POINTER(PG_GETARG_POINTER(0));
}

PG_FUNCTION_INFO_V1(gip4r_decompress);
Datum
gip4r_decompress(PG_FUNCTION_ARGS)
{
    PG_RETURN_POINTER(PG_GETARG_POINTER(0));
}

/*
** The GiST Penalty method for IP ranges
** As in the R-tree paper, we use change in area as our penalty metric
*/
PG_FUNCTION_INFO_V1(gip4r_penalty);
Datum
gip4r_penalty(PG_FUNCTION_ARGS)
{
    GISTENTRY *origentry = (GISTENTRY *) PG_GETARG_POINTER(0);
    GISTENTRY *newentry = (GISTENTRY *) PG_GETARG_POINTER(1);
    float *result = (float *) PG_GETARG_POINTER(2);
    IP4R *key;
    IP4R ud;
    float tmp1, tmp2;

    key = (IP4R *) DatumGetPointer(origentry->key);
    ud = *key;
    tmp2 = ip4r_metric(&ud);

    key = (IP4R *) DatumGetPointer(newentry->key);
    if (key->lower < ud.lower)
	ud.lower = key->lower;
    if (key->upper > ud.upper)
	ud.upper = key->upper;
    tmp1 = ip4r_metric(&ud);

    *result = tmp1 - tmp2;
  
#ifdef GIST_DEBUG
    fprintf(stderr, "penalty\n");
    fprintf(stderr, "\t%g\n", *result);
#endif
  
    PG_RETURN_POINTER(result);
}


/* Helper functions for picksplit. We might need to sort a list of
 * ranges by size; these are for that.
 */

struct gip4r_sort
{
    IP4R *key;
    OffsetNumber pos;
};

static int
gip4r_sort_compare(const void *a, const void *b)
{
    double sa = ip4r_metric(((struct gip4r_sort *)a)->key);
    double sb = ip4r_metric(((struct gip4r_sort *)b)->key);
    return (sa > sb) ? 1 : ((sa == sb) ? 0 : -1);
}

/*
** The GiST PickSplit method for IP ranges
** This is a linear-time algorithm based on a left/right split,
** based on the box functions in rtree_gist simplified to one
** dimension
*/
PG_FUNCTION_INFO_V1(gip4r_picksplit);
Datum
gip4r_picksplit(PG_FUNCTION_ARGS)
{
    GistEntryVector *entryvec = (GistEntryVector *) PG_GETARG_POINTER(0);
    GIST_SPLITVEC *v = (GIST_SPLITVEC *) PG_GETARG_POINTER(1);
    GISTENTRY *ent = GISTENTRYVEC(entryvec);
    OffsetNumber i;
    int	nbytes;
    OffsetNumber maxoff;
    OffsetNumber *listL;
    OffsetNumber *listR;
    bool allisequal = true;
    IP4R pageunion;
    IP4R *cur;
    IP4R *unionL;
    IP4R *unionR;
    int posL = 0;
    int posR = 0;

    posL = posR = 0;
    maxoff = GISTENTRYCOUNT(entryvec) - 1;

    cur = (IP4R *) DatumGetPointer(ent[FirstOffsetNumber].key);
    pageunion = *cur;

    /* find MBR */
    for (i = OffsetNumberNext(FirstOffsetNumber); i <= maxoff; i = OffsetNumberNext(i))
    {
	cur = (IP4R *) DatumGetPointer(ent[i].key);
	if (allisequal == true
	    && (pageunion.lower != cur->lower || pageunion.upper != cur->upper))
	    allisequal = false;

	if (cur->lower < pageunion.lower)
	    pageunion.lower = cur->lower;
	if (cur->upper > pageunion.upper)
	    pageunion.upper = cur->upper;
    }

    nbytes = (maxoff + 2) * sizeof(OffsetNumber);
    listL = (OffsetNumber *) palloc(nbytes);
    listR = (OffsetNumber *) palloc(nbytes);
    unionL = (IP4R *) palloc(sizeof(IP4R));
    unionR = (IP4R *) palloc(sizeof(IP4R));
    v->spl_ldatum = PointerGetDatum(unionL);
    v->spl_rdatum = PointerGetDatum(unionR);
    v->spl_left = listL;
    v->spl_right = listR;

    if (allisequal)
    {
	cur = (IP4R *) DatumGetPointer(ent[OffsetNumberNext(FirstOffsetNumber)].key);
	if (ip4r_equal(cur, &pageunion))
	{
	    OffsetNumber split_at = FirstOffsetNumber + (maxoff - FirstOffsetNumber + 1)/2;
	    v->spl_nleft = v->spl_nright = 0;
	    *unionL = pageunion;
	    *unionR = pageunion;

	    for (i = FirstOffsetNumber; i < split_at; i = OffsetNumberNext(i))
		v->spl_left[v->spl_nleft++] = i;
	    for (; i <= maxoff; i = OffsetNumberNext(i))
		v->spl_right[v->spl_nright++] = i;

	    PG_RETURN_POINTER(v);
	}
    }

#define ADDLIST( list_, u_, pos_, num_ ) do { \
	if ( pos_ ) { \
		if ( (u_)->upper < (cur)->upper ) (u_)->upper = (cur)->upper; \
		if ( (u_)->lower > (cur)->lower ) (u_)->lower = (cur)->lower; \
	} else { \
		*(u_) = *(cur); \
	} \
	(list_)[(pos_)++] = (num_); \
} while(0)

    for (i = FirstOffsetNumber; i <= maxoff; i = OffsetNumberNext(i))
    {
	cur = (IP4R *) DatumGetPointer(ent[i].key);
	if (cur->lower - pageunion.lower < pageunion.upper - cur->upper)
	    ADDLIST(listL, unionL, posL, i);
	else
	    ADDLIST(listR, unionR, posR, i);
    }

    /* bad disposition, sort by ascending size and resplit */
    if (posR == 0 || posL == 0)
    {
	struct gip4r_sort *arr = (struct gip4r_sort *)
	    palloc(sizeof(struct gip4r_sort) * (maxoff + FirstOffsetNumber));

	for (i = FirstOffsetNumber; i <= maxoff; i = OffsetNumberNext(i))
	{
	    arr[i].key = (IP4R *) DatumGetPointer(ent[i].key);
	    arr[i].pos = i;
	}

	qsort(arr + FirstOffsetNumber,
	      maxoff - FirstOffsetNumber + 1,
	      sizeof(struct gip4r_sort),
	      gip4r_sort_compare);

	posL = posR = 0;
	for (i = FirstOffsetNumber; i <= maxoff; i = OffsetNumberNext(i))
	{
	    cur = arr[i].key;
	    if (cur->lower - pageunion.lower < pageunion.upper - cur->upper)
		ADDLIST(listL, unionL, posL, arr[i].pos);
	    else if (cur->lower - pageunion.lower == pageunion.upper - cur->upper)
	    {
		if (posL > posR)
		    ADDLIST(listR, unionR, posR, arr[i].pos);
		else
		    ADDLIST(listL, unionL, posL, arr[i].pos);
	    }
	    else
		ADDLIST(listR, unionR, posR, arr[i].pos);
	}
	pfree(arr);
    }

    v->spl_nleft = posL;
    v->spl_nright = posR;

    PG_RETURN_POINTER(v);
}

#undef ADDLIST

/*
** Equality methods
*/
PG_FUNCTION_INFO_V1(gip4r_same);
Datum
gip4r_same(PG_FUNCTION_ARGS)
{
    IP4R *v1 = (IP4R *) PG_GETARG_POINTER(0);
    IP4R *v2 = (IP4R *) PG_GETARG_POINTER(1);
    bool *result = (bool *) PG_GETARG_POINTER(2);

    if (v1 && v2)
	*result = ip4r_equal(v1,v2);
    else
	*result = (v1 == NULL && v2 == NULL);

#ifdef GIST_DEBUG
    fprintf(stderr, "same: %s\n", (*result ? "TRUE" : "FALSE"));
#endif

    PG_RETURN_POINTER(result);
}


/*
 * Strategy numbers:
 *	OPERATOR	1	>>= ,
 *	OPERATOR	2	<<= ,
 *	OPERATOR	3	>> ,
 *	OPERATOR	4	<< ,
 *	OPERATOR	5	&& ,
 *	OPERATOR	6	= ,
 */

/*
** SUPPORT ROUTINES
*/
static bool
gip4r_leaf_consistent(IP4R * key,
		      IP4R * query,
		      StrategyNumber strategy)
{
#ifdef GIST_QUERY_DEBUG
    fprintf(stderr, "leaf_consistent, %d\n", strategy);
#endif
  
    switch (strategy)
    {
	case 1:   /* left contains right nonstrict */
	    return ip4r_contains_internal(key, query, TRUE);
	case 2:   /* left contained in right nonstrict */
	    return ip4r_contains_internal(query, key, TRUE);
	case 3:   /* left contains right strict */
	    return ip4r_contains_internal(key, query, FALSE);
	case 4:   /* left contained in right strict */
	    return ip4r_contains_internal(query, key, FALSE);
	case 5:   /* left overlaps right */
	    return ip4r_overlaps_internal(key, query);
	case 6:   /* left equal right */
	    return ip4r_equal(key, query);
	default:
	    return FALSE;
    }
}

/* logic notes:
 * If the union value we're looking at overlaps with our query value
 * at all, then any of the values underneath it might overlap with us
 * or be contained by us, so all the "contained by" and "overlaps"
 * cases degenerate to "overlap".
 * If the union value is equal to the query value, then none of the
 * values under it can strictly contain the query value, so for
 * "contained" queries the strictness is preserved.
 * If we're looking for an "equal" value, then we have to enter any
 * subtree whose union contains (not strictly) our query value.
 */

bool
gip4r_internal_consistent(IP4R * key,
			  IP4R * query,
			  StrategyNumber strategy)
{
#ifdef GIST_QUERY_DEBUG
    fprintf(stderr, "internal_consistent, %d\n", strategy);
#endif
  
    switch (strategy)
    {
	case 2:   /* left contained in right nonstrict */
	case 4:   /* left contained in right strict */
	case 5:   /* left overlaps right */
	    return ip4r_overlaps_internal(key, query);
	case 3:   /* left contains right strict */
	    return ip4r_contains_internal(key, query, FALSE);
	case 1:   /* left contains right nonstrict */
	case 6:   /* left equal right */
	    return ip4r_contains_internal(key, query, TRUE);
	default:
	    return FALSE;
    }
}

/* end */
