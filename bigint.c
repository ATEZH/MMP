#include "bigint.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

/**
 * INVARIANTS:
 *
 * BigInt capacity and size >= 1
 * BigInt capacity >= size
 * BigInt capacity >= 16
 *
 * For size >= 2, limbs[size - 1] > 0
 * For size <= i < capacity, limbs[i] == 0
 *
 * Canonical zero BigInt has size = 1, limbs[0] = 0, sign = 1
 *
 * BigInt sign is 1 (positive) or -1 (negative)
 *
 * Sign is independent of magnitude (limbs store the absolute value)
 */

#define MIN_CAPACITY 16
#define LOWER_32_BITS(n) ((n) & 0xFFFFFFFF)
#define UPPER_32_BITS(n) (n >> 32)
#define CHUNK_SHIFT (uint32_t)1000000000
#define CHUNK_DIGITS 9

int is_space(char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\v' || c == '\f' || c == '\r';
}

uint32_t count_ones(uint32_t x) {
    x = x - ((x >> 1) & 0x55555555);
    x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
    x = (x + (x >> 4)) & 0x0F0F0F0F;
    x = x + (x >> 8);
    x = x + (x >> 16);
    return x & 0x3F;
}

uint32_t count_leading_zeros(uint32_t x) {
    x |= (x >> 1);
    x |= (x >> 2);
    x |= (x >> 4);
    x |= (x >> 8);
    x |= (x >> 16);
    return 32 - count_ones(x);
}

void grow_capacity(BigInt bigint) {
    assert(bigint != NULL);
    int32_t new_capacity = bigint->capacity * 2;
    uint32_t *new_limbs = realloc(bigint->limbs, new_capacity * sizeof(*new_limbs));
    if (new_limbs == NULL) {
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    bigint->limbs = new_limbs;
    bigint->capacity = new_capacity;
    for (int i = bigint->size; i < bigint->capacity; i++) {
        bigint->limbs[i] = 0;
    }
}

void grow_capacity_to(BigInt bigint, int32_t new_capacity) {
    assert(bigint != NULL);
    if (bigint->capacity >= new_capacity) {
        return;
    }
    uint32_t *new_limbs = realloc(bigint->limbs, new_capacity * sizeof(uint32_t));
    if (new_limbs == NULL) {
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    bigint->capacity = new_capacity;
    bigint->limbs = new_limbs;
    for (int i = bigint->size; i < bigint->capacity; i++) {
        bigint->limbs[i] = 0;
    }
}

void zero_bigint(BigInt bigint) {
    assert(bigint != NULL);
    assert(bigint->limbs != NULL);
    for (int i = 0; i < bigint->size; i++) {
        bigint->limbs[i] = 0;
    }
    bigint->size = 1;
    bigint->sign = 1;
}

void positive_one_bigint(BigInt bigint) {
    assert(bigint != NULL);
    for (int i = 1; i < bigint->size; i++) {
        bigint->limbs[i] = 0;
    }
    bigint->limbs[0] = 1;
    bigint->size = 1;
    bigint->sign = 1;
}

int bigint_sign(BigInt bigint) {
    assert(bigint != NULL);
    return bigint->sign;
}

int bigint_is_zero(BigInt bigint) {
    assert(bigint != NULL);
    assert(bigint->limbs != NULL);
    return bigint->size == 1 && bigint->limbs[0] == 0 && bigint->sign == 1;
}

int bigint_is_abs_one(BigInt bigint) {
    assert(bigint != NULL);
    return bigint->size == 1 && bigint->limbs[0] == 1 && bigint->sign == 1;
}

/**
 * For all the bigint comparison functions:
 *  0 if op1 = op2;
 * -1 if op1 < op2;
 *  1 if op1 > op2;
 */
int bigint_cmp(BigInt op1, BigInt op2) {
    assert(op1 != NULL);
    assert(op2 != NULL);
    if (op1 == op2)
        return 0;
    if (op1->sign != op2->sign)
        return op1->sign;
    else if (op1->size != op2->size)
        return op1->size > op2->size ? op1->sign : -op1->sign;
    int i = op1->size - 1;
    while (i >= 0 && op1->limbs[i] == op2->limbs[i])
        i--;
    if (i < 0)
        return 0;
    else
        return op1->limbs[i] > op2->limbs[i] ? op1->sign : -op1->sign;
}

int bigint_cmp_uint64(BigInt op1, uint64_t op2) {
    assert(op1 != NULL);
    if (op1->sign == -1)
        return -1;
    else if (op1->size > 2)
        return 1;
    uint64_t op1_magnitude = (uint64_t) op1->limbs[0] | ((op1->size == 2 ? (uint64_t) op1->limbs[1] : 0) << 32);
    if (op1_magnitude == op2)
        return 0;
    return (op1_magnitude > op2) ? op1->sign : -op1->sign;
}

int bigint_cmp_int64(BigInt op1, int64_t op2) {
    assert(op1 != NULL);
    if ((op1->sign == -1 && op2 >= 0) || (op1->sign == 1 && op2 < 0) || op1->size > 2)
        return op1->sign;
    uint64_t op1_magnitude = (uint64_t) op1->limbs[0] | ((op1->size == 2 ? (uint64_t) op1->limbs[1] : 0) << 32);
    uint64_t op2_magnitude = op2 * op1->sign;
    if (op1_magnitude == op2_magnitude)
        return 0;
    return (op1_magnitude > op2_magnitude) ? op1->sign : -op1->sign;
}

int bigint_abs_cmp_uint64(BigInt op1, uint64_t op2) {
    assert(op1 != NULL);
    if (op1->size > 2)
        return 1;
    uint64_t op1_magnitude = (uint64_t) op1->limbs[0] | ((op1->size == 2 ? (uint64_t) op1->limbs[1] : 0) << 32);
    if (op1_magnitude == op2)
        return 0;
    return (op1_magnitude > op2) ? op1->sign : -op1->sign;
}

int bigint_abs_cmp_int64(BigInt op1, int64_t op2) {
    assert(op1 != NULL);
    uint64_t op2_magnitude = op2 * op1->sign;
    return bigint_abs_cmp_uint64(op1, op2_magnitude);
}

int bigint_abs_cmp(BigInt op1, BigInt op2) {
    assert(op1 != NULL);
    assert(op2 != NULL);
    if (op1 == op2)
        return 0;
    if (op1->size != op2->size)
        return op1->size > op2->size ? 1 : -1;
    int i = op1->size - 1;
    while (i >= 0 && op1->limbs[i] == op2->limbs[i])
        i--;
    if (i < 0)
        return 0;
    else
        return op1->limbs[i] > op2->limbs[i] ? 1 : -1;
}

void bigint_abs_add_uint32(BigInt rop, BigInt op1, uint32_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    rop->size = op1->size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size * 2);
    }
    uint64_t result = (uint64_t) op1->limbs[0] + op2;
    uint8_t carry = UPPER_32_BITS(result);
    rop->limbs[0] = LOWER_32_BITS(result);
    int i = 1;
    for (; i < op1->size && carry; i++) {
        rop->limbs[i] = op1->limbs[i] + carry;
        carry = rop->limbs[i] == 0;
    }
    if (rop != op1) {
        for (; i < op1->size; i++) {
            rop->limbs[i] = op1->limbs[i];
        }
    }
    if (carry) {
        rop->limbs[rop->size++] = carry;
    }
}

/**
 * Assumes that op1 > op2
 */
void bigint_abs_sub_uint32(BigInt rop, BigInt op1, uint32_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    rop->size = op1->size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size + 1);
    }
    uint64_t result = (uint64_t) op1->limbs[0] - op2;
    rop->limbs[0] = LOWER_32_BITS(result);
    uint8_t borrow = (result >> 63) & 1;
    int i = 1;
    for (; i < op1->size && borrow; i++) {
        rop->limbs[i] = op1->limbs[i] - borrow;
        borrow = rop->limbs[i] == BASE - 1;
    }
    if (rop != op1) {
        for (; i < op1->size; i++) {
            rop->limbs[i] = op1->limbs[i];
        }
    }
}

void bigint_add_uint32(BigInt rop, BigInt op1, uint32_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    if (op1->sign == 1) {
        rop->sign = op1->sign;
        bigint_abs_add_uint32(rop, op1, op2);
    } else {
        int cmp = bigint_abs_cmp_uint64(op1, op2);
        if (cmp == 0) {
            zero_bigint(rop);
            return;
        } else if (cmp == -1) {
            uint32_t tmp = op1->limbs[0];
            op1->limbs[0] = op2;
            op2 = tmp;
        }
        rop->sign = -cmp;
        bigint_abs_sub_uint32(rop, op1, op2);
    }
}

void bigint_sub_uint32(BigInt rop, BigInt op1, uint32_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    if (op1->sign == 1) {
        int cmp = bigint_abs_cmp_uint64(op1, op2);
        if (cmp == 0) {
            zero_bigint(rop);
            return;
        } else if (cmp == -1) {
            uint32_t tmp = op1->limbs[0];
            op1->limbs[0] = op2;
            op2 = tmp;
        }
        rop->sign = cmp;
        bigint_abs_sub_uint32(rop, op1, op2);
    } else {
        rop->sign = op1->sign;
        bigint_abs_add_uint32(rop, op1, op2);
    }
}

void bigint_abs_add_uint64(BigInt rop, BigInt op1, uint64_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    rop->size = op1->size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size * 2);
    }
    uint64_t first_two_limbs = ((uint64_t)op1->limbs[1] << 32) | op1->limbs[0];
    uint64_t result = first_two_limbs + op2;
    uint8_t carry = result < first_two_limbs + op2;
    rop->limbs[0] = LOWER_32_BITS(result);
    rop->limbs[1] = UPPER_32_BITS(result);
    if (rop->limbs[1] > 1 && rop->size == 1) {
        rop->size++;
    }
    int i = 2;
    for (; i < op1->size && carry; i++) {
        rop->limbs[i] = op1->limbs[i] + carry;
        carry = rop->limbs[i] == 0;
    }
    if (rop != op1) {
        for (; i < op1->size; i++) {
            rop->limbs[i] = op1->limbs[i];
        }
    }
    if (carry) {
        rop->limbs[rop->size++] = carry;
    }
}

void bigint_abs_sub_uint64(BigInt rop, BigInt op1, uint64_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    rop->size = op1->size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size + 1);
    }
    uint64_t first_two_limbs = ((uint64_t)op1->limbs[1] << 32) | op1->limbs[0];
    uint64_t result = first_two_limbs - op2;
    uint8_t borrow = result > first_two_limbs + op2;
    rop->limbs[0] = LOWER_32_BITS(result);
    rop->limbs[1] = UPPER_32_BITS(result);
    int i = 2;
    for (; i < op1->size && borrow; i++) {
        rop->limbs[i] = op1->limbs[i] - borrow;
        borrow = rop->limbs[i] == BASE - 1;
    }
    if (rop != op1) {
        for (; i < op1->size; i++) {
            rop->limbs[i] = op1->limbs[i];
        }
    }
    if (rop->limbs[rop->size - 1] == 0 && rop->size > 1) {
        rop->size--;
    }
    if (rop->size == 1 && rop->limbs[0] == 0) {
        rop->sign = 1;
    }
}

void bigint_add_uint64(BigInt rop, BigInt op1, uint64_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    if (op1->sign == 1) {
        rop->sign = op1->sign;
        bigint_abs_add_uint64(rop, op1, op2);
    } else {
        int cmp = bigint_abs_cmp_uint64(op1, op2);
        if (cmp == 0) {
            zero_bigint(rop);
            return;
        } else if (cmp == -1) {
            uint64_t tmp = ((uint64_t)op1->limbs[1] << 32) | op1->limbs[0];
            op1->limbs[0] = LOWER_32_BITS(tmp);
            op1->limbs[1] = UPPER_32_BITS(tmp);
            op2 = tmp;
            op1->size += op1->limbs[1] > 0 && op1->size == 1;
        }
        rop->sign = -cmp;
        bigint_abs_sub_uint32(rop, op1, op2);
    }
}

void bigint_sub_uint64(BigInt rop, BigInt op1, uint64_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    if (op1->sign == 1) {
        int cmp = bigint_abs_cmp_uint64(op1, op2);
        if (cmp == 0) {
            zero_bigint(rop);
            return;
        } else if (cmp == -1) {
            uint64_t tmp = ((uint64_t)op1->limbs[1] << 32) | op1->limbs[0];
            op1->limbs[0] = LOWER_32_BITS(tmp);
            op1->limbs[1] = UPPER_32_BITS(tmp);
            op2 = tmp;
            op1->size += op1->limbs[1] > 0 && op1->size == 1;
        }
        rop->sign = cmp;
        bigint_abs_sub_uint32(rop, op1, op2);
    } else {
        rop->sign = op1->sign;
        bigint_abs_add_uint64(rop, op1, op2);
    }
}

void bigint_abs_add(BigInt rop, BigInt op1, BigInt op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    assert(op2 != NULL);
    if (op1->size < op2->size) {
        BigInt tmp = op1;
        op1 = op2;
        op2 = tmp;
    }
    rop->size = op1->size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size * 2);
    }
    uint8_t carry = 0;
    uint64_t result = 0;
    int i = 0;
    for (; i < op2->size; i++) {
        result = (uint64_t) op1->limbs[i] + op2->limbs[i] + carry;
        rop->limbs[i] = LOWER_32_BITS(result);
        carry = UPPER_32_BITS(result);
    }
    for (; i < op1->size && carry; i++) {
        rop->limbs[i] = op1->limbs[i] + carry;
        carry = rop->limbs[i] == 0;
    }
    if (rop != op1) {
        for (; i < op1->size; i++) {
            rop->limbs[i] = op1->limbs[i];
        }
    }
    if (carry) {
        rop->limbs[rop->size++] = carry;
    }
}

/**
 * Assumes that op1 > op2
 */
void bigint_abs_sub(BigInt rop, BigInt op1, BigInt op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    assert(op2 != NULL);
    rop->size = op1->size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size + 1);
    }
    uint64_t result = 0;
    uint8_t borrow = 0;
    int i = 0;
    for (; i < op2->size; i++) {
        result = (uint64_t) op1->limbs[i] - op2->limbs[i] - borrow;
        rop->limbs[i] = LOWER_32_BITS(result);
        borrow = (result >> 63) & 1;
    }
    for (; i < op1->size && borrow; i++) {
        rop->limbs[i] = op1->limbs[i] - borrow;
        borrow = rop->limbs[i] == BASE - 1;
    }
    if (rop != op1) {
        for (; i < op1->size; i++) {
            rop->limbs[i] = op1->limbs[i];
        }
    }
    for (i = rop->size - 1; i > 0 && rop->limbs[i] == 0; i--) {
        rop->size--;
    }
    if (rop->size == 1 && rop->limbs[0] == 0) {
        rop->sign = 1;
    }
}

void bigint_add(BigInt rop, BigInt op1, BigInt op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    assert(op2 != NULL);
    if (op1->sign == op2->sign) {
        rop->sign = op1->sign;
        bigint_abs_add(rop, op1, op2);
    } else {
        int cmp = bigint_abs_cmp(op1, op2);
        if (cmp == 0) {
            zero_bigint(rop);
            return;
        } else if (cmp == -1) {
            BigInt tmp = op1;
            op1 = op2;
            op2 = tmp;
        }
        rop->sign = cmp == -1 ? op2->sign : op1->sign;
        bigint_abs_sub(rop, op1, op2);
    }
}

void bigint_sub(BigInt rop, BigInt op1, BigInt op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    assert(op2 != NULL);
    if (op1->sign == op2->sign) {
        int cmp = bigint_abs_cmp(op1, op2);
        if (cmp == 0) {
            zero_bigint(rop);
            return;
        } else if (cmp == -1) {
            BigInt tmp = op1;
            op1 = op2;
            op2 = tmp;
        }
        rop->sign = cmp == -1 ? op2->sign : op1->sign;
        bigint_abs_sub(rop, op1, op2);
    } else {
        rop->sign = op1->sign;
        bigint_abs_add(rop, op1, op2);
    }
}

void bigint_mul_uint32(BigInt rop, BigInt op1, uint32_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    if (op2 == 0 || bigint_is_zero(op1)) {
        zero_bigint(rop);
        return;
    } else if (op2 == 1) {
        bigint_copy(rop, op1);
        return;
    }
    rop->size = op1->size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size * 2);
    }
    uint32_t carry = 0;
    uint64_t result = 0;
    for (int i = 0; i < op1->size; ++i) {
        result = (uint64_t) (op2) * op1->limbs[i] + carry;
        rop->limbs[i] = LOWER_32_BITS(result);
        carry = UPPER_32_BITS(result);
    }
    if (carry) {
        rop->limbs[rop->size++] = carry;
    }
}

void bigint_mul(BigInt rop, BigInt op1, BigInt op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    assert(op2 != NULL);
    if (bigint_is_zero(op1) || bigint_is_zero(op2)) {
        zero_bigint(rop);
        return;
    } else if (bigint_is_abs_one(op1) || bigint_is_abs_one(op2)) {
        bigint_copy(rop, bigint_is_abs_one(op1) ? op2 : op1);
        rop->sign = (op1->sign == op2->sign) ? 1 : -1;
        return;
    } else if (op1->size == 1 || op2->size == 1) {
        bigint_mul_uint32(
            rop,
            op1->size == 1 ? op2 : op1,
            op1->size == 1 ? op1->limbs[0] : op2->limbs[0]
        );
        rop->sign = (op1->sign == op2->sign) ? 1 : -1;
        return;
    }
    rop->sign = (op1->sign == op2->sign) ? 1 : -1;
    int op1_size = op1->size;
    int op2_size = op2->size;
    rop->size = op1_size + op2_size;
    if (rop->capacity <= rop->size) {
        rop->capacity = rop->size * 2;
    }
    uint32_t *new_limbs = calloc(rop->capacity, sizeof(uint32_t));
    if (new_limbs == NULL) {
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    for (int i = 0; i < op2_size; i++) {
        uint64_t result = 0;
        uint32_t carry = 0;
        for (int j = 0; j < op1_size; j++) {
            result = (uint64_t) (op1->limbs[j]) * op2->limbs[i] + new_limbs[i + j] + carry;
            new_limbs[i + j] = LOWER_32_BITS(result);
            carry = UPPER_32_BITS(result);
        }
        new_limbs[op1_size + i] = carry;
    }
    if (new_limbs[rop->size] > 0) {
        rop->size++;
    }
    free(rop->limbs);
    rop->limbs = new_limbs;
}

void bigint_div_uint32(BigInt quotient, BigInt remainder, BigInt op1, uint32_t op2) {
    assert(quotient != NULL);
    assert(remainder != NULL);
    assert(quotient->limbs != NULL);
    assert(remainder->limbs != NULL);
    assert(op1 != NULL);
    if (op2 == 0) {
        fprintf(stderr, "BigInt Error: Division by zero;\n");
        abort();
    }
    quotient->size = op1->size;
    if (quotient->capacity <= quotient->size + 1) {
        grow_capacity_to(quotient, quotient->size + 1);
    }
    uint32_t d_remainder = 0;
    uint64_t dividend = 0;
    for (int32_t i = op1->size - 1; i >= 0; i--) {
        dividend = ((uint64_t) d_remainder << 32) | op1->limbs[i];
        quotient->limbs[i] = dividend / op2;
        d_remainder = dividend % op2;
    }
    if (remainder->size > 1) {
        zero_bigint(remainder);
    }
    remainder->limbs[0] = d_remainder;
    remainder->sign = quotient->sign;
    if (quotient->limbs[quotient->size - 1] == 0 && quotient->size > 1) {
        quotient->size--;
    }
    if (quotient->size == 1 && quotient->limbs[0] == 0) {
        quotient->sign = 1;
    }
}

// Taken from: https://skanthak.hier-im-netz.de/division.html#divmnu
void bigint_div(BigInt quotient, BigInt remainder, BigInt op1, BigInt op2) {
    assert(quotient != NULL);
    assert(remainder != NULL);
    assert(quotient != remainder);
    assert(op1 != NULL);
    assert(op2 != NULL);
    assert(!bigint_is_zero(op2));
    if (op2->size == 1) {
        bigint_div_uint32(quotient, remainder, op1, op2->limbs[0]);
        int sign = (op1->sign == op2->sign) ? 1 : -1;
        quotient->sign = sign;
        return;
    }
    int cmp = bigint_abs_cmp(op1, op2);
    if (cmp == -1) {
        zero_bigint(quotient);
        bigint_copy(remainder, op1);
        return;
    } else if (cmp == 0) {
        positive_one_bigint(quotient);
        quotient->sign = (op1->sign == op2->sign) ? 1 : -1;
        zero_bigint(remainder);
        return;
    }
    int32_t m = op1->size;
    int32_t n = op2->size;
    remainder->size = n;
    if (remainder->capacity <= remainder->size + 1) {
        grow_capacity_to(remainder, remainder->size + 1);
    }
    quotient->size = m + 1;
    if (quotient->capacity <= quotient->size + 1) {
        grow_capacity_to(quotient, quotient->size + 1);
    }
    uint32_t s = count_leading_zeros(op2->limbs[n - 1]);
    uint32_t *u = malloc((m + 1) * sizeof(*u));
    uint32_t *v = malloc(n * sizeof(*v));
    for (int32_t i = n - 1; i > 0; i--) {
        v[i] = (op2->limbs[i] << s) | (op2->limbs[i - 1] >> (31 - s) >> 1);
    }
    v[0] = op2->limbs[0] << s;
    u[m] = op1->limbs[m - 1] >> (31 - s) >> 1;
    for (int32_t i = m - 1; i > 0; i--) {
        u[i] = (op1->limbs[i] << s) | (op1->limbs[i - 1] >> (31 - s) >> 1);
    }
    u[0] = op1->limbs[0] << s;
    quotient->size = m - n + 1;
    for (int32_t j = m - n; j >= 0; j--) {
        uint64_t q_hat = (u[j + n] * BASE + u[j + n - 1]) / v[n - 1];
        uint64_t r_hat = (u[j + n] * BASE + u[j + n]) % v[n - 1];
        while (q_hat >= BASE || (unsigned) q_hat * (uint64_t) v[n - 2] > BASE * r_hat + u[j + n - 2]) {
            q_hat--;
            r_hat += v[n - 1];
            if (r_hat >= BASE) break;
        }
        int64_t k = 0;
        int64_t t;
        uint64_t p;
        for (int i = 0; i < n; i++) {
            p = (unsigned) q_hat * (uint64_t) v[i];
            t = u[i + j] - k - LOWER_32_BITS(p);
            u[i + j] = t;
            k = UPPER_32_BITS(p) - UPPER_32_BITS(t);
        }
        t = u[j + n] - k;
        u[j + n] = t;
        quotient->limbs[j] = q_hat;
        if (t < 0) {
            quotient->limbs[j]--;
            k = 0;
            for (int i = 0; i < n; i++) {
                t = (uint64_t) u[i + j] + v[i] + k;
                u[i + j] = t;
                k = t >> 32;
            }
            u[j + n] += k;
        }
    }
    for (int i = 0; i < n - 1; i++) {
        remainder->limbs[i] = (u[i] >> s) | (u[i+1] << (31-s) << 1);
    }
    remainder->limbs[n - 1] = u[n - 1] >> s;
    if (quotient->limbs[quotient->size - 1] == 0 && quotient->size > 1) {
        quotient->size--;
    }
    if (remainder->limbs[remainder->size - 1] == 0 && remainder->size > 1) {
        remainder->size--;
    }
    free(u);
    free(v);
}

void bigint_copy(BigInt dst, BigInt src) {
    assert(dst != NULL);
    assert(src != NULL);
    assert(src != dst);
    if (dst->capacity <= src->size) {
        grow_capacity_to(dst, src->capacity);
    }
    dst->size = src->size;
    dst->sign = src->sign;
    for (int i = 0; i < src->size; i++) {
        dst->limbs[i] = src->limbs[i];
    }
    for (int i = src->size; i < dst->capacity; i++) {
        dst->limbs[i] = 0;
    }
}

void bigint_destroy(BigInt bigint) {
    assert(bigint != NULL);
    assert(bigint->limbs != NULL);
    free(bigint->limbs);
    free(bigint);
}

void print_bigint_limbs(BigInt bigint) {
    assert(bigint != NULL);
    for (int i = bigint->size - 1; i >= 1; --i) {
        if (bigint->limbs[i])
            printf("%u*2^%d + ", bigint->limbs[i], i * 32);
    }
    printf("%u*2^%d\n", bigint->limbs[0], 0);
}

char *bigint_to_str(BigInt bigint) {
    assert(bigint != NULL);
    char *result;
    if (bigint_is_zero(bigint)) {
        result = strdup("0");
        if (result == NULL) {
            fprintf(stderr, "Fatal: Out of memory;\n");
            abort();
        }
        return result;
    }
    BigInt temp = bigint_init();
    BigInt remainder = bigint_init();
    bigint_copy(temp, bigint);

    size_t buffer_size = (bigint->size * sizeof(*bigint->limbs) * 3) + 10;
    char *str_buffer = malloc(buffer_size);
    if (str_buffer == NULL) {
        bigint_destroy(temp);
        bigint_destroy(remainder);
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    char chunk_buffer[CHUNK_DIGITS + 1];
    char *ptr = str_buffer + buffer_size - 1;
    *ptr = '\0';
    while (!bigint_is_zero(temp)) {
        bigint_div_uint32(temp, remainder, temp, CHUNK_SHIFT);
        ptr -= CHUNK_DIGITS;
        snprintf(chunk_buffer, CHUNK_DIGITS + 1, "%0*u", CHUNK_DIGITS, remainder->limbs[0]);
        memcpy(ptr, chunk_buffer, CHUNK_DIGITS * sizeof(char));
    }
    while (*ptr == '0' && *(ptr + 1) != '\0') ptr++;
    if (bigint->sign == -1) {
        *(--ptr) = '-';
    }

    bigint_destroy(temp);
    bigint_destroy(remainder);
    result = strdup(ptr);
    free(str_buffer);
    if (result == NULL) {
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    return result;
}

BigInt bigint_init(void) {
    BigInt bigint = malloc(sizeof(struct BigInt_S));
    if (bigint == NULL) {
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    bigint->limbs = malloc(MIN_CAPACITY * sizeof(uint32_t));
    if (bigint->limbs == NULL) {
        free(bigint);
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    bigint->capacity = MIN_CAPACITY;
    bigint->sign = 1;
    bigint->size = 1;
    for (int i = 0; i < MIN_CAPACITY; i++) {
        bigint->limbs[i] = 0;
    }
    return bigint;
}

BigInt bigint_init_from_uint64(uint64_t val, int sign) {
    BigInt bigint = malloc(sizeof(struct BigInt_S));
    if (bigint == NULL) {
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    bigint->limbs = malloc(MIN_CAPACITY * sizeof(uint32_t));
    if (bigint->limbs == NULL) {
        free(bigint);
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    bigint->capacity = MIN_CAPACITY;
    sign = (sign >= 0) ? 1 : -1;
    bigint->sign = sign;
    bigint->limbs[0] = LOWER_32_BITS(val);
    bigint->limbs[1] = UPPER_32_BITS(val);
    for (int i = 2; i < MIN_CAPACITY; i++) {
        bigint->limbs[i] = 0;
    }
    bigint->size += 1 + (bigint->limbs[1] > 0);
    return bigint;
}

BigInt bigint_init_from_str(char *str) {
    assert(str != NULL);
    BigInt bigint = malloc(sizeof(struct BigInt_S));
    if (bigint == NULL) {
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    bigint->capacity = MIN_CAPACITY;
    bigint->sign = 1;
    bigint->size = 1;
    bigint->limbs = calloc(MIN_CAPACITY, sizeof(uint32_t));
    if (bigint->limbs == NULL) {
        free(bigint);
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    for (int i = 0; i < MIN_CAPACITY; i++) {
        bigint->limbs[i] = 0;
    }
    size_t digits = strlen(str), i = 0;
    while (i < digits && is_space(str[i]))
        ++i;
    bigint->sign = str[i] == '-' ? -1 : 1;
    i += str[i] == '-' || str[i] == '+';
    size_t cutoff = digits - ((digits - i) / CHUNK_DIGITS) * CHUNK_DIGITS;
    for (; i < digits; cutoff += CHUNK_DIGITS) {
        uint32_t chunk = 0;
        for (; i < cutoff; ++i) {
            if (str[i] < '0' || str[i] > '9') { // stop if a character that isn't a digit is encountered
                if (bigint_is_zero(bigint)) {
                    bigint->sign = 1;
                }
                return bigint;
            }
            chunk = chunk * 10 + (str[i] - '0');
        }
        bigint_mul_uint32(bigint, bigint, CHUNK_SHIFT);
        bigint_add_uint32(bigint, bigint, chunk);
    }
    if (bigint_is_zero(bigint)) {
        bigint->sign = 1;
    }
    return bigint;
}
