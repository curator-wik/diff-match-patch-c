/**
 * dmp.c
 *
 * C language implementation of Google Diff, Match, and Patch library
 *
 * Original library is Copyright (c) 2006 Google Inc.
 * http://code.google.com/p/google-diff-match-patch/
 *
 * Copyright (c) Russell Belfer <rb@github.com>
 * https://github.com/arrbee/google-diff-match-patch-c/
 *
 * See included LICENSE file for license details.
 *
 *******************************************************************************************
 * Copyright (c) Juan Gonzalez <supergusano2@gmail.com> under same license as Russell Belfer
 * my own contributions nearly transliterated from google-diff-match-patch
 * so that license is included below too
 *******************************************************************************************
 *
 * Diff Match and Patch
 *
 * Copyright 2006 Google Inc.
 * http://code.google.com/p/google-diff-match-patch/
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 *   Unless required by applicable law or agreed to in writing, software
 *   distributed under the License is distributed on an "AS IS" BASIS,
 *   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *   See the License for the specific language governing permissions and
 *   limitations under the License.
 *   """
 *
 *   """Functions for diff, match and patch.
 *
 *   Computes the difference between two texts to create a patch.
 *   Applies the patch onto another text, allowing for errors.
 *
 */

#include "dmp.h"
#include "dmp_pool.h"
#include <sys/types.h>
#include <stdlib.h>
#include <assert.h>
#include <ctype.h>
#include <stdint.h>
#include <string.h>
#include <stdarg.h>
#include <stdbool.h>

#define dmp_min(A,B)      (((A) < (B)) ? (A) : (B))
#define dmp_max(A,B)      (((A) > (B)) ? (A) : (B))
#define dmp_num_cmp(A,B)  (((A) < (B)) ? -1 : ((A) > (B)) ? 1 : 0)

#define START_POOL	8

struct dmp_diff {
	dmp_pool pool;
	dmp_range list;
	double deadline;
	/* original parameters */
	const char *t1, *t2;
	uint32_t l1, l2;
	/* used by bisect */
	int *v1, *v2;
	uint32_t v_alloc;
};

static double dmp_time(void);

static int diff_main(
	dmp_range *, dmp_diff *, const dmp_options *,
	const char *, uint32_t, const char *, uint32_t);

static int diff_bisect(
	dmp_range *, dmp_diff *, const dmp_options *,
	const char *, uint32_t, const char *, uint32_t);

static int diff_cleanup_merge(dmp_diff *diff, dmp_range *list);

static dmp_diff *alloc_diff(const dmp_options *opts)
{
	dmp_diff *diff = malloc(sizeof(dmp_diff));
	if (!diff)
		return NULL;

	memset(diff, 0, sizeof(*diff));

	diff->deadline = (opts && opts->timeout > 0) ?
		dmp_time() + opts->timeout : -1.0;

	if (dmp_pool_alloc(&diff->pool, START_POOL) < 0) {
		free(diff);
		diff = NULL;
	}

	return diff;
}

int dmp_diff_new(
	dmp_diff **diff_ptr,
	const dmp_options *options,
	const char *text1,
	uint32_t    len1,
	const char *text2,
	uint32_t    len2)
{
	dmp_diff *diff;

	assert(diff_ptr);

	*diff_ptr = diff = alloc_diff(options);
	if (!diff)
		return -1;

	diff->t1 = text1;
	diff->l1 = len1;
	diff->t2 = text2;
	diff->l2 = len2;

	return diff_main(&diff->list, diff, options, text1, len1, text2, len2);
}

int dmp_diff_from_strs(
	dmp_diff **diff,
	const dmp_options *options,
	const char *text1,
	const char *text2)
{
	if (!text1)
		text1 = "";
	if (!text2)
		text2 = "";

	return dmp_diff_new(
		diff, options, text1, (uint32_t)strlen(text1), text2, (uint32_t)strlen(text2));
}

static int diff_main(
	dmp_range  *out,
	dmp_diff  *diff,
	const dmp_options *opts,
	const char *text1,
	uint32_t    len1,
	const char *text2,
	uint32_t    len2)
{
	const char *t_short, *t_long, *found;
	uint32_t l_short, l_long, common;
	dmp_pool *pool = &diff->pool;

	/* check for one-sided diffs */

	if (!text1 || !len1) {
		dmp_range_init(
			pool, out, DMP_DIFF_INSERT, text2, 0, len2);
		return pool->error;
	}

	if (!text2 || !len2) {
		dmp_range_init(
			pool, out, DMP_DIFF_DELETE, text1, 0, len1);
		return pool->error;
	}

	/* allocate sentinel */
	if (dmp_range_init(pool, out, DMP_DIFF_EQUAL, text1, len1, 0) < 0)
		goto finish;

	/* trim common prefix */

	common = dmp_common_prefix(text1, len1, text2, len2);
	if (common > 0) {
		dmp_range_insert(
			pool, out, -1, DMP_DIFF_EQUAL, text1, 0, common);

		text1 += common;
		len1  -= common;
		text2 += common;
		len2  -= common;
	}

	/* trim common suffix */

	common = dmp_common_suffix(text1, len1, text2, len2);
	if (common > 0) {
		dmp_range_insert(
			pool, out, out->end,
			DMP_DIFF_EQUAL, text1, len1 - common, common);

		len1 -= common;
		len2 -= common;
	}

	/* after trimming, check for degenerate cases */

	if (!len1) {
		if (len2)
			dmp_range_insert(
				pool, out, -1, DMP_DIFF_INSERT, text2, 0, len2);
		goto finish;
	} else if (!len2) {
		dmp_range_insert(
			pool, out, -1, DMP_DIFF_DELETE, text1, 0, len1);
		goto finish;
	}

	/* check for "common middle" - i.e. one text inside the other */

	if (len1 <= len2) {
		t_short = text1;
		l_short = len1;
		t_long  = text2;
		l_long  = len2;
	} else {
		t_short = text2;
		l_short = len2;
		t_long  = text1;
		l_long  = len1;
	}

	if ((found = dmp_strstr(t_long, l_long, t_short, l_short)) != NULL) {
		int op = (t_short == text1) ? DMP_DIFF_INSERT : DMP_DIFF_DELETE;
		uint32_t found_at = (uint32_t)(found - t_long);

		dmp_range_insert(
			pool, out, -1, op, t_long, 0, found_at);
		dmp_range_insert(
			pool, out, -1, DMP_DIFF_EQUAL, t_short, 0, l_short);
		found_at += l_short;
		dmp_range_insert(
			pool, out, -1, op, t_long, found_at, l_long - found_at);

		goto finish;
	}

	if (l_short == 1) {
		/* this speed up applies after testing for short inside long above */
		dmp_range_insert(
			pool, out, -1, DMP_DIFF_DELETE, text1, 0, len1);
		dmp_range_insert(
			pool, out, -1, DMP_DIFF_INSERT, text2, 0, len2);
		goto finish;
	}

	/* TODO: "half match" and "line mode" optimizations */

	/* full Myers bisect diff */

	if (!pool->error)
		diff_bisect(out, diff, opts, text1, len1, text2, len2);

	if (!pool->error)
		diff_cleanup_merge(diff, out);

finish:
	dmp_range_normalize(pool, out);

	return pool->error;
}

static int diff_bisect_split(
	dmp_range *out,
	dmp_diff *diff,
	const dmp_options *opts,
	const char *t1,
	int t1pivot,
	uint32_t t1len,
	const char *t2,
	int t2pivot,
	uint32_t t2len)
{
	dmp_range l1, l2;
	int rv = diff_main(&l1, diff, opts, t1, t1pivot, t2, t2pivot);

	if (rv == 0)
		rv = diff_main(&l2, diff, opts,
			t1 + t1pivot, t1len - t1pivot, t2 + t2pivot, t2len - t2pivot);

	if (rv == 0) {
		dmp_range_splice(&diff->pool, out, -1, &l1);
		dmp_range_splice(&diff->pool, out, -1, &l2);
	}

	return rv;
}

/* bisect diff - find "middle snake" of a diff
 * See Myers 1986: An O(ND) Difference Algorithm and Its Variations.
 */
static int diff_bisect(
	dmp_range *out,
	dmp_diff *diff,
	const dmp_options *opts,
	const char *t1,
	uint32_t t1len,
	const char *t2,
	uint32_t t2len)
{
	int max_d, v_offset, v_length, d;
	int delta, front, k1start, k1end, k2start, k2end, *v1, *v2;

	v_offset = max_d = (t1len + t2len + 1) / 2;
	v_length = 2 * max_d;
	delta = (int)t1len - (int)t2len;
	front = (delta % 2 != 0);
	k1start = k1end = k2start = k2end = 0;

	if ((int)diff->v_alloc < v_length) {
		size_t asize = v_length * sizeof(int);
		diff->v1 = diff->v1 ? realloc(diff->v1, asize) : malloc(asize);
		diff->v2 = diff->v2 ? realloc(diff->v2, asize) : malloc(asize);
		diff->v_alloc = v_length;

		if (!diff->v1 || !diff->v2)
			return -1;
	}
	v1 = diff->v1;
	v2 = diff->v2;
	/* initialize arrays to -1 (except v_offset + 1 element to 0) */
	memset(v1, 0xff, v_length * sizeof(int));
	memset(v2, 0xff, v_length * sizeof(int));
	v1[v_offset + 1] = 0;
	v2[v_offset + 1] = 0;

	for (d = 0; d < max_d; d++) {
		int k1, k2;

		/* TODO: bail out if deadline is reached */

		/* advance the front contour */
		for (k1 = -d + k1start; k1 <= d - k1end; k1 += 2) {
			int k1off = v_offset + k1;
			uint32_t x1, y1;

			if (k1 == -d || (k1 != d && v1[k1off - 1] < v1[k1off + 1]))
				x1 = v1[k1off + 1];
			else
				x1 = v1[k1off - 1] + 1;
			y1 = x1 - k1;

			while (x1 < t1len && y1 < t2len && t1[x1] == t2[y1])
				x1++, y1++;

			v1[k1off] = x1;
			if (x1 > t1len) /* ran off the right of the graph */
				k1end += 2;
			else if (y1 > t2len) /* ran off bottom of the graph */
				k1start += 2;
			else if (front) {
				int k2off = v_offset + delta - k1;
				if (k2off >= 0 && k2off < v_length && v2[k2off] != -1) {
					/* mirror x2 onto top-left coordinate system */
					uint32_t x2 = (int)t1len - v2[k2off];
					if (x1 >= x2)
						return diff_bisect_split(
							out, diff, opts, t1, x1, t1len, t2, y1, t2len);
				}
			}
		}

		/* advance the reverse contour */
		for (k2 = -d + k2start; k2 <= d - k2end; k2 += 2) {
			int k2off = v_offset + k2;
			uint32_t x2, y2;

			if (k2 == -d || (k2 != d && v2[k2off - 1] < v2[k2off + 1]))
				x2 = v2[k2off + 1];
			else
				x2 = v2[k2off - 1] + 1;
			y2 = x2 - k2;

			while (x2 < t1len && y2 < t2len &&
				   t1[t1len - x2 - 1] == t2[t2len - y2 - 1])
				x2++, y2++;

			v2[k2off] = x2;
			if (x2 > t1len) /* ran off the left of the graph */
				k2end += 2;
			else if (y2 > t2len) /* ran off top of the graph */
				k2start += 2;
			else if (!front) {
				int k1off = v_offset + delta - k2;
				if (k1off >= 0 && k1off < v_length && v1[k1off] != -1) {
					/* mirror x2 onto top-left coordinate system */
					uint32_t x1 = v1[k1off], y1 = v_offset + x1 - k1off;
					x2 = t1len - x2;
					if (x1 >= x2)
						return diff_bisect_split(
							out, diff, opts, t1, x1, t1len, t2, y1, t2len);
				}
			}
		}
	}

	/* diff took too long or # diffs == # chars (i.e. no commonality) */
	dmp_range_insert(&diff->pool, out, -1, DMP_DIFF_DELETE, t1, 0, t1len);
	dmp_range_insert(&diff->pool, out, -1, DMP_DIFF_INSERT, t2, 0, t2len);

	return diff->pool.error;
}

static int diff_cleanup_merge(dmp_diff *diff, dmp_range *list)
{
	dmp_pool *pool = &diff->pool;
	int i, j, before, common, changes;
	int count_delete, count_insert, len_delete, len_insert;
	dmp_node *ins = NULL, *del = NULL, *last = NULL, *node, *next;

	count_insert = count_delete = 0;
	len_insert = len_delete = 0;
	before = -1;

	dmp_range_normalize(pool, list);

	/* ensure EQUAL at end to guarantee termination of cleanup passes */
	node = dmp_node_at(pool, list->end);
	if (node->op != DMP_DIFF_EQUAL)
		dmp_range_insert(
			pool, list, -1, DMP_DIFF_EQUAL, node->text, node->len, 0);

	/* first pass - look for groups of consecutive inserts and deletes
	 * that can be merged or that have unnoticed common prefixes/suffixes
	 * that can be extracted
	 */

	for (i = list->start; i != -1; i = j) {
		node = dmp_node_at(pool, i);
        j = node->next;

		switch (node->op) {
		case DMP_DIFF_INSERT:
			count_insert++;
			len_insert += node->len;
			if (!ins)
				ins = node;
			else {
				last->next = node->next; /* collapse node */
				dmp_node_release(pool, i);
			}
			break;
		case DMP_DIFF_DELETE:
			count_delete++;
			len_delete += node->len;
			if (!del)
				del = node;
			else {
				last->next = node->next; /* collapse node */
				dmp_node_release(pool, i);
			}
			break;
		case DMP_DIFF_EQUAL:
			if (count_delete + count_insert > 0) {
				if (count_delete > 0 && count_insert > 0) {
					/* factor out common prefix */
					common = dmp_common_prefix(
						ins->text, len_insert, del->text, len_delete);

					if (common > 0) {
						if (before == -1) {
							dmp_range_insert(pool, list, 0,
								DMP_DIFF_EQUAL, ins->text, 0, common);
						} else {
							last = dmp_node_at(pool, before);
							last->len += common;
						}
						ins->text  += common;
						len_insert -= common;
						del->text  += common;
						len_delete -= common;
					}

					/* factor out common suffix */
					common = dmp_common_suffix(
						ins->text, len_insert, del->text, len_delete);
					if (common > 0) {
						node->text -= common;
						node->len  += common;
						len_insert -= common;
						len_delete -= common;
					}
				}
				/* merge deletes */
				if (del)
					del->len = len_delete;
				/* merge inserts */
				if (ins)
					ins->len = len_insert;
			}
			else if (last && last->op == DMP_DIFF_EQUAL) {
				/* merge this equality with the previous one */
				last->len += node->len;
				last->next = node->next;
				dmp_node_release(pool, i);
			}

			count_insert = count_delete = 0;
			len_insert = len_delete = 0;
			ins = del = NULL;
			before = i;
			break;
		default:
			/* skip me */
			break;
		}

		last = node;
	}

	/* second pass - look for single edits surrounded by equalities
	 * which can be shifted sideways to eliminate an equality
	 */
	last = dmp_node_at(pool, list->start);
	next = (last->next < 0) ? NULL : dmp_node_at(pool, last->next);
	changes = 0;

	for (i = last->next; next != NULL && i != -1; i = node->next) {
		node = next;
		if (node->next < 0)
			break;
		next = dmp_node_at(pool, node->next);

		if (last->op == DMP_DIFF_EQUAL && next->op == DMP_DIFF_EQUAL) {
			if (last->len > 0 &&
				dmp_has_suffix(node->text, node->len, last->text, last->len))
			{
				node->text -= last->len;
				next->text -= last->len;
				next->len += last->len;
				last->len = 0;
				changes++;
			}
			else if (next->len > 0 &&
				dmp_has_prefix(node->text, node->len, next->text, next->len))
			{
				last->len += next->len;
				node->text += next->len;
				next->len = 0;
				changes++;
			}
		}

		last = node;
	}

	/* remove 0-len nodes */
	dmp_range_normalize(pool, list);

	/* if shifts were made, diff needs reordering and another shift sweep */
	if (changes > 0)
		return diff_cleanup_merge(diff, list);

	return pool->error;
}

void dmp_diff_free(dmp_diff *diff)
{
	free(diff->v1);
	free(diff->v2);
	dmp_pool_free(&diff->pool);
	free(diff);
}

int dmp_diff_foreach(
	const dmp_diff *diff,
	dmp_diff_callback cb,
	void *cb_ref)
{
	int pos, rval = 0;
	const dmp_node *node;

	dmp_range_foreach(&diff->pool, &diff->list, pos, node) {
		if ((rval = cb(cb_ref, node->op, node->text, node->len)) != 0)
			break;
	}

	return rval;
}

uint32_t dmp_diff_hunks(const dmp_diff *diff)
{
	int pos;
	const dmp_node *node;
	uint32_t count = 0;

	dmp_range_foreach(&diff->pool, &diff->list, pos, node)
		count++;

	return count;
}

static void print_bytes(FILE *fp, const char *bytes, uint32_t len)
{
	uint32_t i;

	for (i = 0; i < len; ++i) {
		char ch = bytes[i];
		if (isprint(ch))
			fprintf(fp, "%c", ch);
		else
			fprintf(fp, "\\x%02x", ((unsigned int)ch) & 0x00ffu);
	}
}

void dmp_diff_print_raw(FILE *fp, const dmp_diff *diff)
{
	int pos, ct = 0, ct0 = 0;
	const dmp_node *node;

	fputs("\n> \"", fp);
	print_bytes(fp, diff->t1, diff->l1);
	fputs("\"\n", fp);

	for (pos = diff->list.start; pos >= 0; pos = node->next) {
		node = dmp_node_at(&diff->pool,pos);
		ct0++;
		if (node->len > 0)
			ct++;
		fprintf(fp, "%c\"", (node->op < 0) ? '-' : (node->op > 0) ? '+' : '=');
		print_bytes(fp, node->text, node->len);
		fputs(node->next >= 0 ? "\", " : "\"\n", fp);
	}

	fputs("< \"", fp);
	print_bytes(fp, diff->t2, diff->l2);
	fputs("\"\n", fp);
}

#define PATCH_MARGIN 4
#define MATCH_MAX_BITS 32
static int _asnprintf(char **strp, size_t size, const char *fmt, ...)
{
	size++;
	int bytes_written = 0;
	*strp = calloc(1, size);
	va_list ap;
	va_start(ap, fmt);
	bytes_written = vsnprintf(*strp, size, fmt, ap);
	va_end(ap);
	return bytes_written;
}

#ifndef strlcat
#define strlcat _strlcat
/*	$NetBSD: strlcat.c,v 1.4 2005/05/16 06:55:48 lukem Exp $	*/
/*	from	NetBSD: strlcat.c,v 1.16 2003/10/27 00:12:42 lukem Exp	*/
/*	from OpenBSD: strlcat.c,v 1.10 2003/04/12 21:56:39 millert Exp	*/

/*
 * Copyright (c) 1998 Todd C. Miller <Todd.Miller@courtesan.com>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND TODD C. MILLER DISCLAIMS ALL
 * WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL TODD C. MILLER BE LIABLE
 * FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

static size_t
_strlcat(char *dst, const char *src, size_t siz)
{
	char *d = dst;
	const char *s = src;
	size_t n = siz;
	size_t dlen;

	/* Find the end of dst and adjust bytes left but don't go past end */
	while (n-- != 0 && *d != '\0')
		d++;
	dlen = d - dst;
	n = siz - dlen;

	if (n == 0)
		return(dlen + strlen(s));
	while (*s != '\0') {
		if (n != 1) {
			*d++ = *s;
			n--;
		}
		s++;
	}
	*d = '\0';

	return(dlen + (s - src));	/* count does not include NUL */
}

#endif

// end is not inclusinve
static char *_substring(char *text, int begin, int end)
{
	int idx, count = 0;
	char *substr = malloc(end - begin + 1);
	for(idx = begin; idx < end; idx++) {
		substr[count++] = text[idx];
	}
	substr[count] = 0;
	return substr;
}

static char _get_op(int op)
{
	char real_op;
	if(op < 0) {
		real_op = '-';
	} else if(op > 0) {
		real_op = '+';
	} else {
		real_op = '=';
	}
	return real_op;
}

struct dmp_diff_minor {
	char op;
	char *text;
};

static struct dmp_diff_minor *_get_diff_minor(dmp_node *node)
{
	struct dmp_diff_minor *dm = calloc(1, sizeof(struct dmp_diff_minor));
	_asnprintf(&dm->text, node->len, "%s", node->text);
	dm->op = _get_op(node->op);
	return dm;
}

struct dmp_patch {
	struct dmp_diff_minor **diffs;
	int64_t start1;
	int64_t start2;
	int64_t length1;
	int64_t length2;
	int diffs_length;
};

static int _string_match_count(char *sub_string, char *string)
{
	int matches = 0;
	char *temp;
	char *temp_sub_string = strdup(sub_string);
	char *temp_sub_string2 = temp_sub_string;
	while((temp = strtok(temp_sub_string2, string))) {
		temp_sub_string2 = NULL;
		matches++;
	}

	free(temp_sub_string);

	return matches;
}

static void _append_diff(struct dmp_patch *patch, struct dmp_diff_minor *dm)
{
	if(!patch || !dm) {
		return;
	}
	if(!patch->diffs) {
		patch->diffs_length = 1;
		patch->diffs = calloc(1, sizeof(struct dmp_diff_minor *));
		patch->diffs[0] = dm;
		return;
	}
	patch->diffs_length++;
	patch->diffs = realloc(patch->diffs,
	    patch->diffs_length * sizeof(struct dmp_diff_minor *));
	patch->diffs[patch->diffs_length - 1] = dm;
}

static void _prepend_diff(struct dmp_patch *patch, struct dmp_diff_minor *dm)
{
	if(!patch || !dm) {
		return;
	}
	if(!patch->diffs) {
		patch->diffs_length = 1;
		patch->diffs = calloc(1, sizeof(struct dmp_diff_minor *));
		patch->diffs[0] = dm;
		return;
	}
	patch->diffs_length++;
	patch->diffs = realloc(patch->diffs,
	    patch->diffs_length * sizeof(struct dmp_diff_minor *));
	int idx;
	for(idx = patch->diffs_length - 1; idx > 0; idx--) {
		patch->diffs[idx] = patch->diffs[idx - 1];
	}
	patch->diffs[0] = dm;
}

static void _patch_add_context(struct dmp_patch *patch, char *text)
{
	if(!strlen(text)) {
		return;
	}

	int padding;
	char *pattern, *prefix, *suffix;

	pattern = _substring(text, patch->start2, patch->start2 + patch->length1);
	padding = 0;

	while(_string_match_count(pattern, text) != 1 &&
	    strlen(pattern) < (MATCH_MAX_BITS - PATCH_MARGIN - PATCH_MARGIN)) {
		padding += PATCH_MARGIN;
		free(pattern);
		pattern = _substring(text, dmp_max(0, patch->start2 - padding),
		    patch->start2 + patch->length1 + padding);
	}

	// "add one chunk for good luck"
	padding += PATCH_MARGIN;

	prefix = _substring(text, dmp_max(0, patch->start2 - padding), patch->start2);
	//prepend prefix to diffs
	struct dmp_diff_minor *dm = calloc(1,
	    sizeof(struct dmp_diff_minor));
	dm->op = '=';
	dm->text = prefix;
	_prepend_diff(patch, dm);

	suffix = _substring(text, patch->start2 + patch->length1,
	    patch->start2 + patch->length1 + padding);
	// append suffix to diffs
	dm = calloc(1, sizeof(struct dmp_diff_minor));
	dm->op = '=';
	dm->text = suffix;
	_append_diff(patch, dm);

	// roll back start points
	patch->start1 -= strlen(prefix);
	patch->start2 -= strlen(prefix);

	// extend lengths
	patch->length1 += strlen(prefix) + strlen(suffix);
	patch->length2 += strlen(prefix) + strlen(suffix);

	free(pattern);
}

// frees patch_text
static char *_create_patch_text(char op, int char_count2, char *patch_text,
    char *diff_text)
{
	char *final_patch_text = NULL;
	char *temp1, *temp2;
	if(op == '+') {
		temp1 = _substring(patch_text, 0, char_count2);
		temp2 = _substring(patch_text, char_count2, strlen(patch_text));
		asprintf(&final_patch_text, "%s%s%s", temp1, diff_text, temp2);
	} else if(op == '-') {
		temp1 = _substring(patch_text, 0, char_count2);
		temp2 = _substring(patch_text, char_count2 + strlen(diff_text),
		    strlen(patch_text));
		asprintf(&final_patch_text, "%s%s", temp1, temp2);
	}

	free(temp1);
	free(temp2);
	free(patch_text);
	return final_patch_text;
}

static char *_url_encode(char *text)
{
	const char *dont_encode = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_.!~*'();/?:@&=+$,# ";
	int idx, jdx, text_len, de_len;
	bool can_encode = false;
	text_len = strlen(text);
	de_len = strlen(dont_encode);

	char *ret_str = calloc(4, text_len);
	for(idx = 0; idx < text_len; idx++) {
		char buf[10] = {0};
		can_encode = true;
		for(jdx = 0; jdx < de_len; jdx++) {
			if(text[idx] == dont_encode[jdx]) {
				can_encode = false;
			}
		}
		if(can_encode) {
			snprintf(buf, sizeof(char) * 4, "%%%02X", text[idx]);
		} else {
			sprintf(buf, "%c", text[idx]);
		}
		strlcat(ret_str, buf, 4 * text_len);
	}

	return ret_str;

}

const char *dmp_diff_get_patch_str(const dmp_diff *diff)
{
	if(!diff) {
		return NULL;
	}
	int pos;
	const dmp_node *node;
	int count = 0;
	int char_count1 = 0, char_count2 = 0;
	int num_patches_allocated = 0;
	struct dmp_patch *patches;

	char *prepatch_text, *postpatch_text;
	prepatch_text = strdup(diff->t1);
	postpatch_text = strdup(diff->t1);

	// we'll need no more than one patch per dmp_node, so we'll allocate that much
	// we probably won't use it all, but this will get freed soon anyway
	for(pos = diff->list.start; pos >= 0; pos = node->next) {
		count++;
		node = dmp_node_at(&diff->pool, pos);
	}
	num_patches_allocated = count;
	if(count == 0) {
		return NULL;
	}
	patches = calloc(count, sizeof(struct dmp_patch));

	count = 0;
	for(pos = diff->list.start; pos >= 0; pos = node->next) {
		bool appended_diff = true;
		node = dmp_node_at(&diff->pool, pos);
		struct dmp_diff_minor *dm = _get_diff_minor(node);
		//printf("%c - %s\n", op, buf);
		if(patches[count].diffs_length == 0 && dm->op != '=') {
			patches[count].start1 = char_count1;
			patches[count].start2 = char_count2;
		}

		switch(dm->op) {
			case '+':
			_append_diff(&patches[count], dm);
			patches[count].length2 += strlen(dm->text);
			postpatch_text = _create_patch_text(dm->op, char_count2,
			    postpatch_text, dm->text);
			break;
			case '-':
			patches[count].length1 += strlen(dm->text);
			_append_diff(&patches[count], dm);
			postpatch_text = _create_patch_text(dm->op, char_count2,
			    postpatch_text, dm->text);
			break;
			case '=':
			if(strlen(dm->text) <= 2 * PATCH_MARGIN &&
			    patches[count].diffs_length != 0 &&
			    num_patches_allocated != count + 1) {
				_append_diff(&patches[count], dm);
				patches[count].length1 += strlen(dm->text);
				patches[count].length2 += strlen(dm->text);
			} else {
				appended_diff = false;
			}

			if(strlen(dm->text) >= 2 * PATCH_MARGIN) {
				if(patches[count].diffs_length != 0) {
					_patch_add_context(&patches[count], prepatch_text);
					count++;
					free(prepatch_text);
					prepatch_text = strdup(postpatch_text);
					char_count1 = char_count2;
				}
			}
			break;
		}
		if(dm->op != '+') {
			char_count1 += strlen(dm->text);
		}
		if(dm->op != '-') {
			char_count2 += strlen(dm->text);
		}
		if(!appended_diff) {
			free(dm->text);
			free(dm);
		}

	}

	if(patches[count].diffs_length != 0) {
		_patch_add_context(&patches[count], prepatch_text);
		count++;
	}

	free(prepatch_text);
	free(postpatch_text);

	const char *final_text = NULL;
	int idx, jdx;
	for(idx = 0; idx < count; idx++) {
		char *coords1, *coords2, *text;
		if(patches[idx].length1 == 0) {
			asprintf(&coords1, "%ld,0", patches[idx].start1);
		} else if(patches[idx].length1 == 1) {
			asprintf(&coords1, "%ld",  patches[idx].start1 + 1);
		} else {
			asprintf(&coords1, "%ld,%ld", patches[idx].start1,
			    patches[idx].length1);
		}
		if(patches[idx].length2 == 0) {
			asprintf(&coords2, "%ld,0", patches[idx].start2);
		} else if(patches[idx].length2 == 1) {
			asprintf(&coords2, "%ld", patches[idx].start2 + 1);
		} else {
			asprintf(&coords2, "%ld,%ld", patches[idx].start2,
			    patches[idx].length2);
		}
		asprintf(&text, "@@ -%s +%s @@\n", coords1, coords2);
		free(coords1);
		free(coords2);
		int text_size = strlen(text) + 2048;
		text = realloc(text, text_size);
		for(jdx = 0; jdx < patches[idx].diffs_length; jdx++) {
			if(patches[idx].diffs[jdx]->op == '+') {
				strlcat(text, "+", text_size);
			} else if(patches[idx].diffs[jdx]->op == '-') {
				strlcat(text, "-", text_size);
			} else {
				strlcat(text, " ", text_size);
			}
			if(text_size < (strlen(text) +
			    strlen(patches[idx].diffs[jdx]->text))) {
				text_size = strlen(text) +
				    strlen(patches[idx].diffs[jdx]->text) * 2;
				text = realloc(text, text_size);
			}
			char *proper_text = _url_encode(patches[idx].diffs[jdx]->text);
			strlcat(proper_text, "\n", strlen(proper_text) * 2);
			strlcat(text, proper_text, text_size);
			free(proper_text);
		}
		if(!final_text) {
			asprintf(&final_text, "%s\n", text);
		} else {
			char *temp_text;
			asprintf(&temp_text, "%s%s\n", final_text, text);
			free(final_text);
			final_text = temp_text;
		}
		free(text);

	}

	for(idx = 0; idx < count; idx++) {
		for (jdx = 0; jdx < patches[idx].diffs_length; jdx++) {
			free(patches[idx].diffs[jdx]->text);
			free(patches[idx].diffs[jdx]);
		}
		free(patches[idx].diffs);
	}
	free(patches);

	return final_text;
}

void dmp_diff_print_patch(FILE *fp, const dmp_diff *diff)
{
	const char *s = dmp_diff_get_patch_str(diff);
	if(s) {
		fprintf(fp, "%s", s);
		free(s);
	}
}

int dmp_options_init(dmp_options *opts)
{
	opts->timeout = 1.0F;
	opts->edit_cost = 4;
	opts->match_threshold = 0.5F;
	opts->match_distance = 1000.0F;
	opts->patch_delete_threshold = 0.5F;
	opts->patch_margin = 4;
	opts->match_maxbits = 32;
	opts->check_lines = 1;
	opts->trim_common_prefix = 1;
	opts->trim_common_suffix = 1;
	return 0;
}

uint32_t dmp_common_prefix(
	const char *t1, uint32_t l1, const char *t2, uint32_t l2)
{
	const char *start = t1;
	const char *end   = t1 + dmp_min(l1, l2);

	for (; t1 < end && *t1 == *t2; t1++, t2++);

	return (uint32_t)(t1 - start);
}

uint32_t dmp_common_suffix(
	const char *t1, uint32_t l1, const char *t2, uint32_t l2)
{
	const char *start;

	if (l1 > l2) {
		const char *tswap = t1; t1 = t2; t2 = tswap;
		uint32_t lswap = l1; l1 = l2; l2 = lswap;
	}

	start = t1;

	for (t1 = t1+l1-1, t2 = t2+l2-1; t1 >= start && *t1 == *t2; t1--, t2--);

	return (uint32_t)((start + l1 - 1) - t1);
}

int dmp_strcmp(
	const char *t1, uint32_t l1, const char *t2, uint32_t l2)
{
	int cmp = memcmp(t1, t2, dmp_min(l1, l2));
	return (cmp != 0) ? cmp : dmp_num_cmp(l1, l2);
}

int dmp_has_prefix(
	const char *text, uint32_t tlen, const char *pfx, uint32_t plen)
{
	if (plen > tlen)
		return 0;

	for (; plen > 0; --plen, ++text, ++pfx)
		if (*text != *pfx)
			return 0;

	return 1;
}

int dmp_has_suffix(
	const char *text, uint32_t tlen, const char *sfx, uint32_t slen)
{
	if (slen > tlen)
		return 0;

	for (text = text + tlen - 1, sfx = sfx + slen - 1;
		 slen > 0; --slen, --text, --sfx)
		if (*text != *sfx)
			return 0;

	return 1;
}

/* Railgun is a fast memmem search */

/* All Railgun variants are written by Georgi 'Kaze', they are free,
 * however I expect the user to mention its homepage, that is:
 * http://www.sanmayce.com/Railgun/index.html
 *
 * Author's email: sanmayce@sanmayce.com
 *
 * Caution: For better speed the case 'if (cbPattern==1)' was removed,
 * so Pattern must be longer than 1 char.
 */
static const char *Railgun_Doublet(
	const char * pbTarget, const char * pbPattern,
	uint32_t cbTarget, uint32_t cbPattern)
{
	const char * pbTargetMax = pbTarget + cbTarget;
	register uint32_t ulHashPattern;
	uint32_t count, countSTATIC;

	if (cbPattern > cbTarget) return(NULL);

	countSTATIC = cbPattern-2;

	pbTarget = pbTarget+cbPattern;
	ulHashPattern = (*(uint16_t *)(pbPattern));

	for ( ;; ) {
		if ( ulHashPattern == (*(uint16_t *)(pbTarget-cbPattern)) ) {
			count = countSTATIC;
			while ( count && *(char *)(pbPattern+2+(countSTATIC-count)) == *(char *)(pbTarget-cbPattern+2+(countSTATIC-count)) ) {
				count--;
			}
			if ( count == 0 ) return((pbTarget-cbPattern));
		}
		pbTarget++;
		if (pbTarget > pbTargetMax) return(NULL);
	}
}

const char *dmp_strstr(
	const char *haystack, uint32_t lh, const char *needle, uint32_t ln)
{
	switch (ln) {
	case 0:
		return haystack;
	case 1:
		return memchr(haystack, *needle, lh);
	default:
		return Railgun_Doublet(haystack, needle, lh, ln);
	}
}

/*
 * Platform specific stuff
 */

#ifdef _WIN32

#include <windows.h>

static double dmp_time(void)
{
    LARGE_INTEGER counter, freq;
    QueryPerformanceCounter(&counter);
    QueryPerformanceFrequency(&freq);
    return (double)counter.QuadPart / (double)freq.QuadPart;
}

#else

#include <sys/time.h>

static double dmp_time(void)
{
	struct timeval tv;
    struct timezone tz;
    gettimeofday(&tv, &tz);
    return (double)tv.tv_sec + tv.tv_usec * 1E-6;
}

#endif

