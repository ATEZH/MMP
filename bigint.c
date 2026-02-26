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
 * For size > 1, limbs[size - 1] > 0
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

#define BYTE_TO_BINARY_PATTERN "%c%c%c%c%c%c%c%c"
#define BYTE_TO_BINARY(byte)  \
  ((byte) & 0x80 ? '1' : '0'), \
  ((byte) & 0x40 ? '1' : '0'), \
  ((byte) & 0x20 ? '1' : '0'), \
  ((byte) & 0x10 ? '1' : '0'), \
  ((byte) & 0x08 ? '1' : '0'), \
  ((byte) & 0x04 ? '1' : '0'), \
  ((byte) & 0x02 ? '1' : '0'), \
  ((byte) & 0x01 ? '1' : '0')

int is_space(char c);

uint32_t count_ones(uint32_t x);

uint32_t count_leading_zeros(uint32_t x);

void grow_capacity(BigInt bigint);

void grow_capacity_to(BigInt bigint, int32_t new_capacity);

int bigint_is_abs_one(BigInt bigint);

void bigint_abs_add_uint32(BigInt rop, BigInt op1, uint32_t op2);

void bigint_abs_sub_uint32(BigInt rop, BigInt op1, uint32_t op2);

void bigint_abs_add_uint64(BigInt rop, BigInt op1, uint64_t op2);

void bigint_abs_sub_uint64(BigInt rop, BigInt op1, uint64_t op2);

void bigint_abs_add(BigInt rop, BigInt op1, BigInt op2);

void bigint_abs_sub(BigInt rop, BigInt op1, BigInt op2);


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
}

void zero_bigint(BigInt bigint) {
    assert(bigint != NULL);
    assert(bigint->limbs != NULL);
    bigint->limbs[0] = 0;
    bigint->size = 1;
    bigint->sign = 1;
}

void positive_one_bigint(BigInt bigint) {
    assert(bigint != NULL);
    bigint->limbs[0] = 1;
    bigint->size = 1;
    bigint->sign = 1;
}

int bigint_sign(BigInt bigint) {
    assert(bigint != NULL);
    return bigint->sign;
}

void bigint_negate(BigInt bigint) {
    assert(bigint != NULL);
    bigint->sign = -bigint->sign;
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
    return (op1_magnitude > op2) ? 1 : -1;
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
    int32_t op1_size = op1->size;
    rop->size = op1->size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size * 2);
    }
    uint64_t result = (uint64_t) op1->limbs[0] + op2;
    uint8_t carry = UPPER_32_BITS(result);
    rop->limbs[0] = LOWER_32_BITS(result);
    int i = 1;
    for (; i < op1_size && carry; i++) {
        rop->limbs[i] = op1->limbs[i] + carry;
        carry = rop->limbs[i] == 0;
    }
    if (rop != op1) {
        for (; i < op1_size; i++) {
            rop->limbs[i] = op1->limbs[i];
        }
    }
    if (carry) {
        rop->limbs[rop->size++] = carry;
    }
}

void bigint_abs_sub_uint32(BigInt rop, BigInt op1, uint32_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    int32_t op1_size = op1->size;
    rop->size = op1->size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size + 1);
    }
    uint64_t result = (uint64_t) op1->limbs[0] - op2;
    rop->limbs[0] = LOWER_32_BITS(result);
    uint8_t borrow = (result >> 63) & 1;
    int i = 1;
    for (; i < op1_size && borrow; i++) {
        rop->limbs[i] = op1->limbs[i] - borrow;
        borrow = rop->limbs[i] == BASE - 1;
    }
    if (rop != op1) {
        for (; i < op1_size; i++) {
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
        if (cmp == -1 && rop != op1) {
            op1->limbs[0] = op2;
        }
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
        if (cmp == -1 && rop != op1) {
            op1->limbs[0] = op2;
        }
    } else {
        rop->sign = op1->sign;
        bigint_abs_add_uint32(rop, op1, op2);
    }
}

void bigint_abs_add_uint64(BigInt rop, BigInt op1, uint64_t op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    int32_t op1_size = op1->size;
    rop->size = op1->size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size * 2);
    }
    uint64_t first_two_limbs = ((uint64_t) op1->limbs[1] << 32) | op1->limbs[0];
    uint64_t result = first_two_limbs + op2;
    uint8_t carry = result < first_two_limbs + op2;
    rop->limbs[0] = LOWER_32_BITS(result);
    rop->limbs[1] = UPPER_32_BITS(result);
    if (rop->limbs[1] > 0 && rop->size == 1) {
        rop->size++;
    }
    int i = 2;
    for (; i < op1_size && carry; i++) {
        rop->limbs[i] = op1->limbs[i] + carry;
        carry = rop->limbs[i] == 0;
    }
    if (rop != op1) {
        for (; i < op1_size; i++) {
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
    int32_t op1_size = op1->size;
    rop->size = op1_size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size + 1);
    }
    uint64_t first_two_limbs = ((uint64_t) op1->limbs[1] << 32) | op1->limbs[0];
    uint64_t result = first_two_limbs - op2;
    uint8_t borrow = result > first_two_limbs + op2;
    rop->limbs[0] = LOWER_32_BITS(result);
    rop->limbs[1] = UPPER_32_BITS(result);
    int i = 2;
    for (; i < op1_size && borrow; i++) {
        rop->limbs[i] = op1->limbs[i] - borrow;
        borrow = rop->limbs[i] == BASE - 1;
    }
    if (rop != op1) {
        for (; i < op1_size; i++) {
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
            uint64_t tmp = ((uint64_t) op1->limbs[1] << 32) | op1->limbs[0];
            op1->limbs[0] = LOWER_32_BITS(op2);
            op1->limbs[1] = UPPER_32_BITS(op2);
            op2 = tmp;
            op1->size = (op1->limbs[1] > 0) + 1;
        }
        rop->sign = -cmp;
        bigint_abs_sub_uint64(rop, op1, op2);
        if (cmp == -1 && rop != op1) {
            op1->limbs[0] = LOWER_32_BITS(op2);
            op1->limbs[1] = UPPER_32_BITS(op2);
            op1->size = (op1->limbs[1] > 0) + 1;
        }
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
            uint64_t tmp = ((uint64_t) op1->limbs[1] << 32) | op1->limbs[0];
            op1->limbs[0] = LOWER_32_BITS(tmp);
            op1->limbs[1] = UPPER_32_BITS(tmp);
            op2 = tmp;
            op1->size = (op1->limbs[1] > 0) + 1;
        }
        rop->sign = cmp;
        bigint_abs_sub_uint32(rop, op1, op2);
        if (cmp == -1 && rop != op1) {
            op1->limbs[0] = LOWER_32_BITS(op2);
            op1->limbs[1] = UPPER_32_BITS(op2);
            op1->size = (op1->limbs[1] > 0) + 1;
        }
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
    int32_t op1_size = op1->size;
    int32_t op2_size = op2->size;
    rop->size = op1_size;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size * 2);
    }
    uint8_t carry = 0;
    uint64_t result = 0;
    int i = 0;
    for (; i < op2_size; i++) {
        result = (uint64_t) op1->limbs[i] + op2->limbs[i] + carry;
        rop->limbs[i] = LOWER_32_BITS(result);
        carry = UPPER_32_BITS(result);
    }
    for (; i < op1_size && carry; i++) {
        rop->limbs[i] = op1->limbs[i] + carry;
        carry = rop->limbs[i] == 0;
    }
    if (rop != op1) {
        for (; i < op1_size; i++) {
            rop->limbs[i] = op1->limbs[i];
        }
    }
    if (carry) {
        rop->limbs[rop->size++] = carry;
    }
}

void bigint_abs_sub(BigInt rop, BigInt op1, BigInt op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    assert(op2 != NULL);
    int32_t op1_size = op1->size;
    int32_t op2_size = op2->size;
    rop->size = op1_size;
    if (rop->capacity < rop->size + 1) {
        grow_capacity_to(rop, rop->size + 1);
    }
    uint64_t result = 0;
    uint8_t borrow = 0;
    int i = 0;
    for (; i < op2_size; i++) {
        result = (uint64_t) op1->limbs[i] - op2->limbs[i] - borrow;
        rop->limbs[i] = LOWER_32_BITS(result);
        borrow = (result >> 63) & 1;
    }
    for (; i < op1_size && borrow; i++) {
        rop->limbs[i] = op1->limbs[i] - borrow;
        borrow = rop->limbs[i] == BASE - 1;
    }
    if (rop != op1) {
        for (; i < op1_size; i++) {
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
        rop->sign = cmp == -1 ? op2->sign : op1->sign;
        if (cmp == 0) {
            zero_bigint(rop);
            return;
        } else if (cmp == -1) {
            BigInt tmp = op1;
            op1 = op2;
            op2 = tmp;
        }
        bigint_abs_sub(rop, op1, op2);
    }
}

void bigint_sub(BigInt rop, BigInt op1, BigInt op2) {
    assert(rop != NULL);
    assert(op1 != NULL);
    assert(op2 != NULL);
    if (op1->sign == op2->sign) {
        int cmp = bigint_abs_cmp(op1, op2);
        rop->sign = cmp == -1 ? -op2->sign : op1->sign;
        if (cmp == 0) {
            zero_bigint(rop);
            return;
        } else if (cmp == -1) {
            BigInt tmp = op1;
            op1 = op2;
            op2 = tmp;
        }
        bigint_abs_sub(rop, op1, op2);
    } else {
        rop->sign = op1->sign;
        bigint_abs_add(rop, op1, op2);
    }
}

void bigint_shift_left(BigInt rop, BigInt op1, uint32_t bit_c) {
    assert(rop != NULL);
    assert(op1 != NULL);
    int32_t bit_shifts = bit_c % (sizeof(*rop->limbs) * 8);
    int32_t limb_shifts = bit_c / (sizeof(*rop->limbs) * 8);
    if (bigint_is_zero(op1)) {
        zero_bigint(rop);
        return;
    } else if (bit_c == 0) {
        bigint_copy(rop, op1);
        return;
    } else if (op1->size >= INT32_MAX - limb_shifts - 1) {
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    int32_t old_size = rop->size;
    int32_t op1_size = op1->size;
    rop->size = op1->size;
    rop->sign = op1->sign;
    if (rop->capacity <= rop->size + limb_shifts) {
        grow_capacity_to(rop, (rop->size + limb_shifts) * 2);
    }
    int i = op1_size + limb_shifts;
    rop->limbs[i] = op1->limbs[op1_size - 1] >> (31 - bit_shifts) >> 1;
    for (i -= 1; i >= limb_shifts + 1; i--) {
        rop->limbs[i] = (op1->limbs[i - limb_shifts] << bit_shifts) |
                        (op1->limbs[i - limb_shifts - 1] >> (31 - bit_shifts) >> 1);
    }
    rop->limbs[limb_shifts] = op1->limbs[0] << bit_shifts;
    for (i -= 1; i >= 0; i--) {
        rop->limbs[i] = 0;
    }
    rop->size += limb_shifts;
    rop->size += (rop->limbs[rop->size] > 0);
    for (i = rop->size; i < old_size; i++) {
        rop->limbs[i] = 0;
    }
}

void bigint_shift_right(BigInt rop, BigInt op1, uint32_t bit_c) {
    assert(rop != NULL);
    assert(op1 != NULL);
    int32_t bit_shifts = bit_c % (sizeof(*rop->limbs) * 8);
    int32_t limb_shifts = bit_c / (sizeof(*rop->limbs) * 8);
    if (bigint_is_zero(op1) || limb_shifts >= op1->size) {
        zero_bigint(rop);
        return;
    } else if (bit_c == 0) {
        bigint_copy(rop, op1);
        return;
    }
    int32_t old_size = rop->size;
    int32_t op1_size = op1->size;
    rop->size = op1->size;
    rop->sign = op1->sign;
    if (rop->capacity <= rop->size - limb_shifts - 1) {
        grow_capacity_to(rop, rop->size - limb_shifts + 2);
    }
    int i = 0;
    for (; i < op1_size - limb_shifts - 1; i++) {
        rop->limbs[i] = (op1->limbs[i + limb_shifts + 1] << (31 - bit_shifts) << 1) |
                        (op1->limbs[i + limb_shifts] >> bit_shifts);
    }
    rop->limbs[i] = op1->limbs[i + limb_shifts] >> bit_shifts;
    for (i += 1; i < old_size; i++) {
        rop->limbs[i] = 0;
    }
    rop->size = op1_size - limb_shifts;
    if (rop->size > 1 && rop->limbs[rop->size - 1] == 0) {
        rop->size--;
    }
    if (rop->size == 1 && rop->limbs[0] == 0) {
        rop->sign = 1;
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
    int32_t op1_size = op1->size;
    rop->size = op1_size;
    rop->sign = op1->sign;
    if (rop->capacity <= rop->size + 1) {
        grow_capacity_to(rop, rop->size * 2);
    }
    uint32_t carry = 0;
    uint64_t result = 0;
    for (int i = 0; i < op1_size; ++i) {
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
    int sign = (op1->sign == op2->sign) ? 1 : -1;
    if (bigint_is_zero(op1) || bigint_is_zero(op2)) {
        zero_bigint(rop);
        return;
    } else if (bigint_is_abs_one(op1) || bigint_is_abs_one(op2)) {
        bigint_copy(rop, bigint_is_abs_one(op1) ? op2 : op1);
        rop->sign = sign;
        return;
    } else if (op1->size == 1 || op2->size == 1) {
        bigint_mul_uint32(
                rop,
                op1->size == 1 ? op2 : op1,
                op1->size == 1 ? op1->limbs[0] : op2->limbs[0]
        );
        rop->sign = sign;
        return;
    }
    int op1_size = op1->size;
    int op2_size = op2->size;
    rop->size = op1_size + op2_size;
    rop->sign = sign;
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
    } else if (new_limbs[rop->size - 1] == 0) {
        rop->size--;
    }
    free(rop->limbs);
    rop->limbs = new_limbs;
}

void bigint_div_uint32(BigInt quotient, BigInt remainder, BigInt op1, uint32_t op2) {
    assert(quotient != NULL);
    assert(remainder != NULL);
    assert(quotient != remainder);
    assert(op1 != NULL);
    if (op2 == 0) {
        fprintf(stderr, "BigInt Error: Division by zero;\n");
        abort();
    }
    quotient->size = op1->size;
    quotient->sign = op1->sign;
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
    if (quotient->limbs[quotient->size - 1] == 0 && quotient->size > 1) {
        quotient->size--;
    }
    if (quotient->size == 1 && quotient->limbs[0] == 0) {
        quotient->sign = 1;
    }
    if (remainder->size > 1) {
        zero_bigint(remainder);
    }
    remainder->limbs[0] = d_remainder;
    remainder->sign = remainder->limbs[0] == 0 ? 1 : op1->sign;
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
        quotient->sign = (op1->sign == op2->sign || (quotient->size == 1 && quotient->limbs[0] == 0)) ? 1 : -1;
        remainder->sign = (remainder->limbs[0] == 0) ? 1 : op1->sign;
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
    quotient->sign = (op1->sign == op2->sign) ? 1 : -1;
    quotient->size = m - n + 1;
    if (quotient->capacity <= quotient->size + 1) {
        grow_capacity_to(quotient, quotient->size + 1);
    }
    remainder->sign = op1->sign;
    remainder->size = n;
    if (remainder->capacity <= remainder->size + 1) {
        grow_capacity_to(remainder, remainder->size + 1);
    }
    uint32_t shift = count_leading_zeros(op2->limbs[n - 1]);
    uint32_t *dividend = malloc((m + 1) * sizeof(*dividend));
    uint32_t *divisor = malloc(n * sizeof(*divisor));
    for (int32_t i = n - 1; i > 0; i--) {
        divisor[i] = (op2->limbs[i] << shift) | (op2->limbs[i - 1] >> (31 - shift) >> 1);
    }
    divisor[0] = op2->limbs[0] << shift;
    dividend[m] = op1->limbs[m - 1] >> (31 - shift) >> 1;
    for (int32_t i = m - 1; i > 0; i--) {
        dividend[i] = (op1->limbs[i] << shift) | (op1->limbs[i - 1] >> (31 - shift) >> 1);
    }
    dividend[0] = op1->limbs[0] << shift;
    for (int j = m - n; j >= 0; j--) {
        uint64_t q_hat = (dividend[j + n] * BASE + dividend[j + n - 1]) / divisor[n - 1];
        uint64_t r_hat = (dividend[j + n] * BASE + dividend[j + n - 1]) % divisor[n - 1];
        while (q_hat >= BASE || (unsigned) q_hat * (uint64_t) divisor[n - 2] > BASE * r_hat + dividend[j + n - 2]) {
            q_hat--;
            r_hat += divisor[n - 1];
            if (r_hat >= BASE) break;
        }
        uint64_t product = 0;
        int64_t result = 0;
        int64_t carry = 0;
        for (int i = 0; i < n; i++) {
            product = (unsigned) q_hat * (uint64_t) divisor[i];
            result = dividend[i + j] - (carry + LOWER_32_BITS(product));
            dividend[i + j] = result;
            carry = UPPER_32_BITS(product) - UPPER_32_BITS(result);
        }
        result = dividend[j + n] - carry;
        dividend[j + n] = result;

        quotient->limbs[j] = q_hat;
        if (result < 0) {
            quotient->limbs[j]--;
            carry = 0;
            for (int i = 0; i < n; i++) {
                result = (uint64_t) dividend[i + j] + divisor[i] + carry;
                dividend[i + j] = result;
                carry = UPPER_32_BITS(result);
            }
            dividend[j + n] += carry;
        }
    }
    for (int i = 0; i < n - 1; i++) {
        remainder->limbs[i] = (dividend[i] >> shift) | (dividend[i + 1] << (31 - shift) << 1);
    }
    remainder->limbs[n - 1] = dividend[n - 1] >> shift;
    if (quotient->limbs[quotient->size - 1] == 0 && quotient->size > 1) {
        quotient->size--;
    }
    if (remainder->limbs[remainder->size - 1] == 0 && remainder->size > 1) {
        remainder->size--;
    }
    free(dividend);
    free(divisor);
}

void bigint_copy(BigInt dst, BigInt src) {
    assert(dst != NULL);
    assert(src != NULL);
    if (dst == src) {
        return;
    } else if (dst->capacity <= src->size) {
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

void print_bigint_limbs_binary(BigInt bigint) {
    assert(bigint != NULL);
    for (int i = bigint->size - 1; i >= 1; --i) {
        uint32_t l = bigint->limbs[i];
        printf(""BYTE_TO_BINARY_PATTERN""BYTE_TO_BINARY_PATTERN""BYTE_TO_BINARY_PATTERN""BYTE_TO_BINARY_PATTERN" ",
               BYTE_TO_BINARY(l >> 24), BYTE_TO_BINARY(l >> 16), BYTE_TO_BINARY(l >> 8), BYTE_TO_BINARY(l));
    }
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
    bigint->limbs = malloc(MIN_CAPACITY * sizeof(*bigint->limbs));
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
    bigint->limbs = malloc(MIN_CAPACITY * sizeof(*bigint->limbs));
    if (bigint->limbs == NULL) {
        free(bigint);
        fprintf(stderr, "Fatal: Out of memory;\n");
        abort();
    }
    bigint->capacity = MIN_CAPACITY;
    bigint->sign = (sign >= 0) ? 1 : -1;
    bigint->limbs[0] = LOWER_32_BITS(val);
    bigint->limbs[1] = UPPER_32_BITS(val);
    for (int i = 2; i < MIN_CAPACITY; i++) {
        bigint->limbs[i] = 0;
    }
    bigint->size = 1 + (bigint->limbs[1] > 0);
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
    bigint->limbs = calloc(MIN_CAPACITY, sizeof(*bigint->limbs));
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
    int sign = str[i] == '-' ? -1 : 1;
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
    bigint->sign = sign;
    if (bigint_is_zero(bigint)) {
        bigint->sign = 1;
    }
    return bigint;
}
