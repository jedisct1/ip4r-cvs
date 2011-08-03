/* $Id: raw_io.c,v 1.1 2011-08-03 20:16:03 andrewsn Exp $ */

/*
 * Copyright (c) 2011 Andrew Gierth
 *
 * Licensed under the same terms as PostgreSQL itself.
 */

#include "ipr.h"

PG_MODULE_MAGIC;

bool ip4_raw_input(const char *osrc, uint32 *dst)
{
	const unsigned char *src = (const unsigned char *)osrc;
	int digits = 0;
	int octets = 0;
	int ch;
	uint32 octet = 0;
	uint32 tmp = 0;

	for (;;)
	{
		switch ((ch = *src++))
		{
			case '0': case '1': case '2': case '3': case '4':
			case '5': case '6': case '7': case '8': case '9':
				if (digits++ && octet == 0)
					return false;   /* must have been a leading 0, reject */
				octet = (octet * 10) + (ch - '0');
				if (octet > 255)
					return false;
				break;

			case '.':
				if (!digits || ++octets > 3)
					return false;
				tmp = (tmp << 8) | octet;
				digits = 0;
				octet = 0;
				break;

			case 0:
				if (!digits || octets != 3)
					return false;
				tmp = (tmp << 8) | octet;
				*dst = tmp;
				return true;

			default:
				return false;
		}
	}
}

bool ip6_raw_input(const char *osrc, uint64 *dst)
{
	const unsigned char *src = (const unsigned char *)osrc;
	const unsigned char *backtrack = src;
	int ch;
	int digits = 0;
	int words = 0;
	int gap = -1;
	uint16 word = 0;
	uint16 tmp[8];

	/* leading :: needs a special case */
	if (*src == ':')
		if (*++src != ':')
			return false;

	for (;;)
	{
		switch ((ch = *src++))
		{
			case '0': case '1': case '2': case '3': case '4':
			case '5': case '6': case '7': case '8': case '9':
				word = (word << 4) | (ch - '0');
				break;

			case 'a': case 'b': case 'c': case 'd': case 'e': case 'f':
				word = (word << 4) | ((ch - 'a') + 10);
				break;

			case 'A': case 'B': case 'C': case 'D': case 'E': case 'F':
				word = (word << 4) | ((ch - 'A') + 10);
				break;

			case ':':
				if (digits == 0)
				{
					if (gap >= 0)
						return false;
					gap = words;
				}
				else if (!*src)
					return false;   /* trailing : not valid except as :: */

				tmp[words++] = word;
				if (words > 7 && *src)
					return false;
				backtrack = src;
				word = 0;
				digits = 0;
				continue;

			case '.':
				if (words < 1 || words > 6)
					return false;

				{
					uint32 ip4val;
					if (!ip4_raw_input((const char *)backtrack, &ip4val))
						return false;
					tmp[words++] = (ip4val >> 16);
					word = (ip4val & 0xffff);
					digits = 4;
				}

				/* FALLTHROUGH */
			case 0:
				if (digits)
					tmp[words++] = word;
				if (words < 8)
				{
					int i,d;
					if (gap < 0)
						return false;
					d = 8 - words;
					for (i = 7; i > gap+d; --i)
						tmp[i] = tmp[i-d];
					for (; i > gap; --i)
						tmp[i] = 0;
				}
				dst[0] = (((uint64)(tmp[0]) << 48) | ((uint64)(tmp[1]) << 32)
						  | ((uint64)(tmp[2]) << 16) | tmp[3]);
				dst[1] = (((uint64)(tmp[4]) << 48) | ((uint64)(tmp[5]) << 32)
						  | ((uint64)(tmp[6]) << 16) | tmp[7]);
				return true;

			default:
				return false;
		}

		if (++digits > 4)
			return false;
	}
}

int ip4_raw_output(uint32 ip, char *str, int len)
{
    return snprintf(str, len, "%u.%u.%u.%u",
					(ip >> 24)&0xff, (ip >> 16)&0xff, (ip >> 8)&0xff, (ip)&0xff);
}

int ip6_raw_output(uint64 *ip, char *str, int len)
{
	uint16 tmp[8];
	char buf[sizeof("ffff:ffff:ffff:ffff:ffff:ffff:255.255.255.255") + 2];
	char *ptr = buf;
	unsigned flags = (1 << 8);
	int best = -1;
	int best_len = 1;
	int best_end;
	uint16 word;
	int i,j;

	tmp[0] = ip[0] >> 48;
	tmp[1] = ip[0] >> 32;
	tmp[2] = ip[0] >> 16;
	tmp[3] = ip[0];
	tmp[4] = ip[1] >> 48;
	tmp[5] = ip[1] >> 32;
	tmp[6] = ip[1] >> 16;
	tmp[7] = ip[1];

	for (i = 0; i < 8; ++i)
		flags |= (tmp[i] ? (1 << i) : 0);
	for (i = 0; i < 8; ++i, flags >>= 1)
		if ((flags & 1) == 0 && (ffs(flags)-1) > best_len)
			best = i, best_len = ffs(flags)-1;

	best_end = best + best_len - 1;

	if (best == 0)
	{
		if (best_len == 6
			|| (best_len == 5 && tmp[5] == 0xffff))
		{
			ip4_raw_output(((uint32)(tmp[6]) << 16) | tmp[7], buf, sizeof(buf)-2);
			return snprintf(str, len, ":%s:%s",
							(best_len == 5) ? ":ffff" : "",
							buf);
		}
		else if (best_len == 8)
			return snprintf(str, len, "::");
	}

	for (i = 0; i < 8; ++i)
	{
		if (i >= best && i <= best_end)
		{
			if (i == best_end)
				*ptr++ = ':';
			continue;
		}

		if (i > 0)
			*ptr++ = ':';

		word = tmp[i];
		if (!word)
			*ptr++ = '0';
		else
		{
			word = (word >> 8) | (word << 8);
			word = ((word & 0xf0f0) >> 4) | ((word & 0x0f0f) << 4);
			for (j = 0; j < 3; ++j, word >>= 4)
				if (word & 0xf)
					break;
			for (; j < 4; ++j, word >>= 4)
				*ptr++ = ((word & 0xf) > 9) ? ((word & 0xf) + 'a' - 10) : ((word & 0xf) + '0');
		}
	}

	if (best_end == 7)
		*ptr++ = ':';

	*ptr = 0;

	return snprintf(str, len, "%s", buf);
}

