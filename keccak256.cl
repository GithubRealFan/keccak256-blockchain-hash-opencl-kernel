#include <stdio.h>
#include <string.h>
#include <time.h>
#include <algorithm>
#include <cuda_runtime.h>

using std::generate;

void memcpylong(ulong *dst, const unsigned char *src, int sz) {
	int i, j;
	for (i = 0; i < sz / 8; i++) {
		dst[i] = 0;
		for (j = 0; j < 8; j++) {
			dst[i] |= (1ll << (8 * j)) * src[i * 8 + j];
		}
	}
}

void memcpychar(char *dst, const unsigned char *src, int sz) {
	int i;
	for (i = 0; i < sz; i++) {
		dst[i] = src[i];
	}
}

void memsetchar(char *dst, int sz) {
	int i;
	for (i = 0; i < sz; i++) {
		dst[i] = 0;
	}
}

__const unsigned char constants[]  = {
    1, 26, 94, 112, 31, 33, 121, 85, 14, 12, 53, 38, 63, 79, 93, 83, 82, 72, 22, 102, 121, 88, 33, 116,
    1, 6, 9, 22, 14, 20, 2, 12, 13, 19, 23, 15, 4, 24, 21, 8, 16, 5, 3, 18, 17, 11, 7, 10,
    1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
};

unsigned char getConstant(unsigned char type, unsigned char index) {
    return constants[type + index];
}

static ulong get_round_constant(unsigned char round) {
    ulong result = 0;
    unsigned char roundInfo = getConstant(TYPE_ROUND_INFO, round);
    if (roundInfo & (1 << 6)) { result |= ((ulong)1 << 63); }
    if (roundInfo & (1 << 5)) { result |= ((ulong)1 << 31); }
    if (roundInfo & (1 << 4)) { result |= ((ulong)1 << 15); }
    if (roundInfo & (1 << 3)) { result |= ((ulong)1 << 7); }
    if (roundInfo & (1 << 2)) { result |= ((ulong)1 << 3); }
    if (roundInfo & (1 << 1)) { result |= ((ulong)1 << 1); }
    if (roundInfo & (1 << 0)) { result |= ((ulong)1 << 0); }

    return result;
}

void keccak_init(SHA3_CTX *ctx) {
	int i;
	for (i = 0; i < sha3_max_permutation_size; i++) {
		ctx->hash[i] = 0;
	}
	for (i = 0; i < sha3_max_rate_in_qwords; i++) {
		ctx->message[i] = 0;
	}
	ctx->rest = 0;
}

static void keccak_theta(ulong *A) {
    ulong C[5], D[5];
    for (unsigned char i = 0; i < 5; i++) {
        C[i] = A[i];
        for (unsigned char j = 5; j < 25; j += 5) { C[i] ^= A[i + j]; }
    }
    for (unsigned char i = 0; i < 5; i++) {
        D[i] = ROTL64(C[(i + 1) % 5], 1) ^ C[(i + 4) % 5];
    }
    for (unsigned char i = 0; i < 5; i++) {
        for (unsigned char j = 0; j < 25; j += 5) { A[i + j] ^= D[i]; }
    }
}

static void keccak_pi(ulong *A) {
    ulong A1 = A[1];
    for (unsigned char i = 1; i < 24; i++) {
        A[getConstant(TYPE_PI_TRANSFORM, i - 1)] = A[getConstant(TYPE_PI_TRANSFORM, i)];
    }
    A[10] = A1;
}

static void keccak_chi(ulong *A) {
    for (unsigned char i = 0; i < 25; i += 5) {
        ulong A0 = A[0 + i], A1 = A[1 + i];
        A[0 + i] ^= ~A1 & A[2 + i];
        A[1 + i] ^= ~A[2 + i] & A[3 + i];
        A[2 + i] ^= ~A[3 + i] & A[4 + i];
        A[3 + i] ^= ~A[4 + i] & A0;
        A[4 + i] ^= ~A0 & A1;
    }
}

static void sha3_permutation(ulong *state) {
    for (unsigned char round = 0; round < 24; round++) {
        keccak_theta(state);
        for (unsigned char i = 1; i < 25; i++) {
            state[i] = ROTL64(state[i], getConstant(TYPE_RHO_TRANSFORM, i - 1));
        }
        keccak_pi(state);
        keccak_chi(state);
        *state ^= get_round_constant(round);
    }
}

static void sha3_process_block(ulong hash[25], const ulong *block) {
    for (unsigned char i = 0; i < 17; i++) {
        hash[i] ^= le2me_64(block[i]);
    }
    sha3_permutation(hash);
}

void keccak_update(SHA3_CTX *ctx, const unsigned char *msg, uint16 size)
{
	int i;
    uint16 idx = (uint16)ctx->rest;
    ctx->rest = (unsigned)((ctx->rest + size) % BLOCK_SIZE);
    if (idx) {
        uint16 left = BLOCK_SIZE - idx;
       	memcpychar((char*)ctx->message + idx, msg, (size < left ? size : left));
        if (size < left) return;
        sha3_process_block(ctx->hash, ctx->message);
        msg  += left;
        size -= left;
    }

    while (size >= BLOCK_SIZE) {
        uint64_t* aligned_message_block;
        if (IS_ALIGNED_64(msg)) {
            aligned_message_block = (uint64_t*)(void*)msg;
        } else {
            memcpylong(ctx->message, msg, BLOCK_SIZE);
            aligned_message_block = ctx->message;
        }

        sha3_process_block(ctx->hash, aligned_message_block);
        msg  += BLOCK_SIZE;
        size -= BLOCK_SIZE;
    }

    if (size) {
        memcpylong(ctx->message, msg, size); /* save leftovers */
    }
}

void keccak_final(SHA3_CTX *ctx, unsigned char* result)
{
	int i;
    uint16 digest_length = 100 - BLOCK_SIZE / 2;

    memsetchar((char*)ctx->message + ctx->rest, BLOCK_SIZE - ctx->rest);
    
    ((char*)ctx->message)[ctx->rest] |= 0x01;
    ((char*)ctx->message)[BLOCK_SIZE - 1] |= 0x80;

    sha3_process_block(ctx->hash, ctx->message);

    if (result) {
    	unsigned char tmp[32];
    	for (i = 0; i < digest_length; i++) {
    		tmp[i] = (ctx->hash[i / 8] >> (8 * (i % 8))) & 255;
    	}
    	for (i = 12; i < 32; i++) {
    		result[i - 12] = tmp[i];
    	}
    }
}

void keccak256(unsigned char* in, unsigned char* out) {
	SHA3_CTX ctx_keccak;
	keccak_init(&ctx_keccak);
	keccak_update(&ctx_keccak, in + 1, 64);
	keccak_final(&ctx_keccak, out);
}


void formatPrivate(unsigned long* privateLong ,unsigned char *privateKey){
	for(size_t i=0;i<4;i++){
		for(uint j=0;j<8;j++){
			const uchar shift = j * 8;
			const uchar byte = (privateLong[i] >> shift) & 0xFF;
			privateKey[(8*i)+j] = byte;
		}
	}
}
__kernel void getPub(__global unsigned char * pubKeys,__global unsigned long * secKey,__global unsigned char * hash){
	
	ulong idx = get_global_id(0);

	int  len = sizeof(pubKeys);
	secp256k1_pubkey tempPub;
	unsigned char * reversedKey ;
	formatPrivate(&secKey,&reversedKey);
	unsigned char privateKey[32];
	for(int i=0,j=31; j>=0; i++,j--) {
		privateKey[i] = reversedKey[j];
	}
	secp256k1_ec_pubkey_create(&tempPub, privateKey);
	secp256k1_ec_pubkey_serialize(pubKeys, len, &tempPub, SECP256K1_EC_UNCOMPRESSED);

	keccak256(pubKeys,&hash);
	for(uint i=0;i<20;i++){
		printf("%02x",hash[i]);
	}
}
