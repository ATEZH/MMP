#ifndef MMP_BIGINT_H
#define MMP_BIGINT_H

#include <stdint.h>

#define BASE ((uint64_t)1 << 32)

struct BigInt_S {
    int32_t sign;
    int32_t capacity;
    int32_t size;
    uint32_t *limbs;
};

typedef struct BigInt_S* BigInt;

BigInt bigint_init(void);
BigInt bigint_init_from_str(char *str);
BigInt bigint_init_from_uint64(uint64_t val, int sign);
void bigint_copy(BigInt dst, BigInt src);
void bigint_destroy(BigInt bigint);

void print_bigint_limbs(BigInt bigint);
char* bigint_to_str(BigInt bigint);

void zero_bigint(BigInt bigint);
void positive_one_bigint(BigInt bigint);

int bigint_sign(BigInt bigint);
int bigint_is_zero(BigInt bigint);

int bigint_cmp(BigInt op1, BigInt op2);
int bigint_abs_cmp(BigInt op1, BigInt op2);
int bigint_cmp_uint64(BigInt op1, uint64_t op2);
int bigint_abs_cmp_uint64(BigInt op1, uint64_t op2);
int bigint_cmp_int64(BigInt op1, int64_t op2);
int bigint_abs_cmp_int64(BigInt op1, int64_t op2);

void bigint_add_uint32(BigInt rop, BigInt op1, uint32_t op2);
void bigint_add_uint64(BigInt rop, BigInt op1, uint64_t op2);
void bigint_add(BigInt rop, BigInt op1, BigInt op2);

void bigint_sub_uint32(BigInt rop, BigInt op1, uint32_t op2);
void bigint_sub_uint64(BigInt rop, BigInt op1, uint64_t op2);
void bigint_sub(BigInt rop, BigInt op1, BigInt op2);

void bigint_mul_uint32(BigInt rop, BigInt op1, uint32_t op2);
void bigint_mul(BigInt rop, BigInt op1, BigInt op2);

void bigint_div_uint32(BigInt quotient, BigInt remainder, BigInt op1, uint32_t op2);
void bigint_div(BigInt quotient, BigInt remainder, BigInt op1, BigInt op2);

#endif //MMP_BIGINT_H
