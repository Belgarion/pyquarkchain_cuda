#include <climits>
#include <cstdint>
#include <cstring>

#include <array>
#include <chrono>
#include <iostream>
#include <random>
#include <set>

#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

#include "helper_cuda.h"

#include <sys/time.h>
#include <cooperative_groups.h>

#include <unistd.h>

using namespace std;
using namespace __gnu_pbds;


#define MAX_WORKSIZE 128000

typedef
tree<
	uint64_t,
	null_type,
	less<uint64_t>,
	rb_tree_tag,
	tree_order_statistics_node_update>
ordered_set_t;


namespace org {
namespace quarkchain {

__constant__ const uint32_t FNV_PRIME_32 = 0x01000193;
__constant__ const uint64_t FNV_PRIME_64 = 0x100000001b3ULL;
__constant__ const uint32_t ACCESS_ROUND = 64;
__constant__ const uint32_t INIT_SET_ENTRIES = 1024 * 64;


/* Keccak core function */

#define KECCAK_ROUNDS 24

#define ROT_01 36
#define ROT_02 3
#define ROT_03 41
#define ROT_04 18
#define ROT_05 1
#define ROT_06 44
#define ROT_07 10
#define ROT_08 45
#define ROT_09 2
#define ROT_10 62
#define ROT_11 6
#define ROT_12 43
#define ROT_13 15
#define ROT_14 61
#define ROT_15 28
#define ROT_16 55
#define ROT_17 25
#define ROT_18 21
#define ROT_19 56
#define ROT_20 27
#define ROT_21 20
#define ROT_22 39
#define ROT_23 8
#define ROT_24 14

__device__ __constant__ const uint64_t roundconstants[KECCAK_ROUNDS] = {
	0x0000000000000001ULL,
	0x0000000000008082ULL,
	0x800000000000808aULL,
	0x8000000080008000ULL,
	0x000000000000808bULL,
	0x0000000080000001ULL,
	0x8000000080008081ULL,
	0x8000000000008009ULL,
	0x000000000000008aULL,
	0x0000000000000088ULL,
	0x0000000080008009ULL,
	0x000000008000000aULL,
	0x000000008000808bULL,
	0x800000000000008bULL,
	0x8000000000008089ULL,
	0x8000000000008003ULL,
	0x8000000000008002ULL,
	0x8000000000000080ULL,
	0x000000000000800aULL,
	0x800000008000000aULL,
	0x8000000080008081ULL,
	0x8000000000008080ULL,
	0x0000000080000001ULL,
	0x8000000080008008ULL
};

#define ROL64(x, y) (((x) << (y)) | ((x) >> (64 - (y))))

__device__ void keccak_function (uint64_t *state) {
	short i;

	/* Temporary variables to avoid indexing overhead */
	uint64_t a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12;
	uint64_t a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24;

	uint64_t b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12;
	uint64_t b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24;

	uint64_t c0, c1, c2, c3, c4, d;

	a0  = state[0];
	a1  = state[1];
	a2  = state[2];
	a3  = state[3];
	a4  = state[4];
	a5  = state[5];
	a6  = state[6];
	a7  = state[7];
	a8  = state[8];
	a9  = state[9];
	a10 = state[10];
	a11 = state[11];
	a12 = state[12];
	a13 = state[13];
	a14 = state[14];
	a15 = state[15];
	a16 = state[16];
	a17 = state[17];
	a18 = state[18];
	a19 = state[19];
	a20 = state[20];
	a21 = state[21];
	a22 = state[22];
	a23 = state[23];
	a24 = state[24];

	for (i = 0; i < KECCAK_ROUNDS; ++i) {
		/*
		 *			Uses temporary variables and loop unrolling to
		 *					   avoid array indexing and inner loops overhead
		 *							   */

		/* Prepare column parity for Theta step */
		c0 = a0 ^ a5 ^ a10 ^ a15 ^ a20;
		c1 = a1 ^ a6 ^ a11 ^ a16 ^ a21;
		c2 = a2 ^ a7 ^ a12 ^ a17 ^ a22;
		c3 = a3 ^ a8 ^ a13 ^ a18 ^ a23;
		c4 = a4 ^ a9 ^ a14 ^ a19 ^ a24;

		/* Theta + Rho + Pi steps */
		d   = c4 ^ ROL64(c1, 1);
		b0  = d ^ a0;
		b16 = ROL64(d ^ a5,  ROT_01);
		b7  = ROL64(d ^ a10, ROT_02);
		b23 = ROL64(d ^ a15, ROT_03);
		b14 = ROL64(d ^ a20, ROT_04);

		d   = c0 ^ ROL64(c2, 1);
		b10 = ROL64(d ^ a1,  ROT_05);
		b1  = ROL64(d ^ a6,  ROT_06);
		b17 = ROL64(d ^ a11, ROT_07);
		b8  = ROL64(d ^ a16, ROT_08);
		b24 = ROL64(d ^ a21, ROT_09);

		d   = c1 ^ ROL64(c3, 1);
		b20 = ROL64(d ^ a2,  ROT_10);
		b11 = ROL64(d ^ a7,  ROT_11);
		b2  = ROL64(d ^ a12, ROT_12);
		b18 = ROL64(d ^ a17, ROT_13);
		b9  = ROL64(d ^ a22, ROT_14);

		d   = c2 ^ ROL64(c4, 1);
		b5  = ROL64(d ^ a3,  ROT_15);
		b21 = ROL64(d ^ a8,  ROT_16);
		b12 = ROL64(d ^ a13, ROT_17);
		b3  = ROL64(d ^ a18, ROT_18);
		b19 = ROL64(d ^ a23, ROT_19);

		d   = c3 ^ ROL64(c0, 1);
		b15 = ROL64(d ^ a4,  ROT_20);
		b6  = ROL64(d ^ a9,  ROT_21);
		b22 = ROL64(d ^ a14, ROT_22);
		b13 = ROL64(d ^ a19, ROT_23);
		b4  = ROL64(d ^ a24, ROT_24);

		/* Chi + Iota steps */
		a0  = b0  ^ (~b1  & b2) ^ roundconstants[i];
		a1  = b1  ^ (~b2  & b3);
		a2  = b2  ^ (~b3  & b4);
		a3  = b3  ^ (~b4  & b0);
		a4  = b4  ^ (~b0  & b1);

		a5  = b5  ^ (~b6  & b7);
		a6  = b6  ^ (~b7  & b8);
		a7  = b7  ^ (~b8  & b9);
		a8  = b8  ^ (~b9  & b5);
		a9  = b9  ^ (~b5  & b6);

		a10 = b10 ^ (~b11 & b12);
		a11 = b11 ^ (~b12 & b13);
		a12 = b12 ^ (~b13 & b14);
		a13 = b13 ^ (~b14 & b10);
		a14 = b14 ^ (~b10 & b11);

		a15 = b15 ^ (~b16 & b17);
		a16 = b16 ^ (~b17 & b18);
		a17 = b17 ^ (~b18 & b19);
		a18 = b18 ^ (~b19 & b15);
		a19 = b19 ^ (~b15 & b16);

		a20 = b20 ^ (~b21 & b22);
		a21 = b21 ^ (~b22 & b23);
		a22 = b22 ^ (~b23 & b24);
		a23 = b23 ^ (~b24 & b20);
		a24 = b24 ^ (~b20 & b21);
	}

	state[0]  = a0;
	state[1]  = a1;
	state[2]  = a2;
	state[3]  = a3;
	state[4]  = a4;
	state[5]  = a5;
	state[6]  = a6;
	state[7]  = a7;
	state[8]  = a8;
	state[9]  = a9;
	state[10] = a10;
	state[11] = a11;
	state[12] = a12;
	state[13] = a13;
	state[14] = a14;
	state[15] = a15;
	state[16] = a16;
	state[17] = a17;
	state[18] = a18;
	state[19] = a19;
	state[20] = a20;
	state[21] = a21;
	state[22] = a22;
	state[23] = a23;
	state[24] = a24;
}


/*
 * 32-bit FNV function
 */
__device__ __host__ uint32_t fnv32(uint32_t v1, uint32_t v2) {
	return (v1 * FNV_PRIME_32) ^ v2;
}

/*
 * 64-bit FNV function
 */
__device__ __host__ uint64_t fnv64(uint64_t v1, uint64_t v2) {
	return (v1 * FNV_PRIME_64) ^ v2;
}


#define LEFT(x) (items+x->left_offset)
#define RIGHT(x) (items+x->right_offset)
#define HAS_LEFT(x) (x->size_left > 0)
#define HAS_RIGHT(x) (x->size_right > 0)


/*
#define LEFT(x) (x->left)
#define RIGHT(x) (x->right)
#define HAS_LEFT(x) (x->left)
#define HAS_RIGHT(x) (x->right)
*/

typedef struct cuoset {
	uint64_t value;
	/*struct cuoset *left;
	struct cuoset *right;*/
	uint16_t left_offset;
	uint16_t right_offset;
	uint8_t in_use;
	uint8_t height;
	uint16_t size_left;
	uint16_t size_right;
} cuoset;

__device__ __host__ uint32_t cuoset_size(cuoset *s);

__device__ __host__ __forceinline__ uint64_t max(uint64_t a, uint64_t b) {
	return (a>b) ? a : b;
}

__device__ __host__ __forceinline__ uint8_t height(cuoset *p) {
	//if (p == NULL || p->in_use == 0) return 0;
	return p->height;
}

__device__ __host__ cuoset *rightRotate(cuoset *y, cuoset *items) {
	cuoset *x = LEFT(y);
	cuoset *T2 = RIGHT(x);
	/*RIGHT(x) = y;
	LEFT(y) = T2;*/
	x->right_offset = y-items;
	y->left_offset = T2-items;
	y->size_left = x->size_right;
	x->size_right = y->size_left + y->size_right + 1;

	uint8_t yhl = HAS_LEFT(y) ? height(LEFT(y)) : 0;
	uint8_t yhr = HAS_RIGHT(y) ? height(RIGHT(y)) : 0;
	y->height = max(yhl, yhr)+1;
	uint8_t xhl = HAS_LEFT(x) ? height(LEFT(x)) : 0;
	uint8_t xhr = HAS_RIGHT(x) ? height(RIGHT(x)) : 0;
	x->height = max(xhl, xhr)+1;
	return x;
}

__device__ __host__ cuoset *leftRotate(cuoset *x, cuoset *items) {
	cuoset *y = RIGHT(x);
	cuoset *T2 = LEFT(y);
	/*LEFT(y) = x;
	RIGHT(x) = T2;*/
	y->left_offset = x-items;
	x->right_offset = T2-items;
	x->size_right = y->size_left;
	y->size_left = x->size_left + x->size_right + 1;

	uint8_t xhl = HAS_LEFT(x) ? height(LEFT(x)) : 0;
	uint8_t xhr = HAS_RIGHT(x) ? height(RIGHT(x)) : 0;
	x->height = max(xhl, xhr)+1;
	uint8_t yhl = HAS_LEFT(y) ? height(LEFT(y)) : 0;
	uint8_t yhr = HAS_RIGHT(y) ? height(RIGHT(y)) : 0;
	y->height = max(yhl, yhr)+1;
	return y;
}

__device__ __host__ __forceinline__ int8_t getBalance(cuoset *N, cuoset *items) {
	if (N == NULL || N->in_use == 0) return 0;
	uint8_t hl = HAS_LEFT(N) ? height(LEFT(N)) : 0;
	uint8_t hr = HAS_RIGHT(N) ? height(RIGHT(N)) : 0;
	return hl-hr;
}

cuoset *h_unused_item;
uint32_t h_oset_size;
__device__ cuoset *unused_item[MAX_WORKSIZE] = {};
__device__ uint32_t oset_size[MAX_WORKSIZE] = {};
__device__ uint32_t depth = 0;
__device__ __host__ cuoset *cuoset_insert(cuoset *node, uint64_t value, uint32_t gid, cuoset *items) {
	if (node == NULL || node->in_use == 0) {
#ifdef __CUDA_ARCH__
		cuoset *new_node = unused_item[gid];
#else
		cuoset *new_node = h_unused_item;
#endif
		new_node->value = value;
		/*LEFT(new_node) = NULL;
		RIGHT(new_node) = NULL;*/
		new_node->in_use = 1;
		new_node->height = 1;
		new_node->size_left = 0;
		new_node->size_right = 0;
#ifdef __CUDA_ARCH__
		unused_item[gid] = NULL;
		oset_size[gid]++;
#else
		h_unused_item = NULL;
		h_oset_size++;
#endif
		return new_node;
	}

	if (value < node->value) {
		//LEFT(node) = cuoset_insert(LEFT(node), value, gid, items);
		if (HAS_LEFT(node)) {
			node->left_offset = cuoset_insert(LEFT(node), value, gid, items) - items;
		} else {
			node->left_offset = cuoset_insert(NULL, value, gid, items) - items;
		}
		node->size_left++;
	} else if (value > node->value) {
		//RIGHT(node) = cuoset_insert(RIGHT(node), value, gid, items);
		if (HAS_RIGHT(node)) {
			node->right_offset = cuoset_insert(RIGHT(node), value, gid, items) - items;
		} else {
			node->right_offset = cuoset_insert(NULL, value, gid, items) - items;
		}
		node->size_right++;
	} else {
		// Keys equal, discard insert since values need to be unique
		return node;
	}

	uint8_t hl = 0;
	if (HAS_LEFT(node)) hl = height(LEFT(node));
	uint8_t hr = 0;
	if (HAS_RIGHT(node)) hr = height(RIGHT(node));
	node->height = 1 + max(hl, hr);

	int8_t balance = getBalance(node, items);

	if (balance > 1) {
		uint64_t lval = LEFT(node)->value;
		// Left Left case
		if (value < lval) {
			return rightRotate(node, items);
		}

		// Left Right case
		if (value > lval) {
			//LEFT(node) = leftRotate(LEFT(node), items);
			node->left_offset = leftRotate(LEFT(node), items) - items;
			return rightRotate(node, items);
		}
	}

	if (balance < -1) {
		uint64_t rval = RIGHT(node)->value;
		// Right Right case
		if (value > rval) {
			return leftRotate(node, items);
		}

		// Right Left case
		if (value < rval) {
			//RIGHT(node) = rightRotate(RIGHT(node), items);
			node->right_offset = rightRotate(RIGHT(node), items) - items;
			return leftRotate(node, items);
		}
	}

	return node;
}

__device__ __host__ cuoset *minValueNode(cuoset *node, cuoset *items) {
	cuoset *current = node;
	while (HAS_LEFT(current)) {
		current = LEFT(current);
	}
	return current;
}

__device__ __host__ cuoset *cuoset_erase(cuoset *root, cuoset *item, uint32_t gid, cuoset *items) {
	if (root == NULL ||root->in_use == 0 ) return root;

	if (item->value < root->value) {
		//LEFT(root) = cuoset_erase(LEFT(root), item, gid, items);
		root->left_offset = cuoset_erase(LEFT(root), item, gid, items) - items;
		root->size_left--;
	} else if (item->value > root->value) {
		//RIGHT(root) = cuoset_erase(RIGHT(root), item, gid, items);
		root->right_offset = cuoset_erase(RIGHT(root), item, gid, items) - items;
		root->size_right--;
	} else {
		if ( (!HAS_LEFT(root)) || (!HAS_RIGHT(root)) ) {
			cuoset *temp = HAS_LEFT(root) ? LEFT(root) : RIGHT(root);
			//if (temp == NULL || temp->in_use == 0) {
			if (!HAS_LEFT(root) && !HAS_RIGHT(root)) {
				temp = root;
				root = NULL;
			} else {
				*root = *temp;
			}
			temp->in_use = 0;
			temp->left_offset = 0;
			temp->right_offset = 0;
			temp->size_left = 0;
			temp->size_right = 0;
#ifdef __CUDA_ARCH__
			unused_item[gid] = temp;
			oset_size[gid]--;
#else
			h_unused_item = temp;
			h_oset_size--;
#endif
		} else {
			cuoset *temp = minValueNode(RIGHT(root), items);
			root->value = temp->value;
			//RIGHT(root) = cuoset_erase(RIGHT(root), temp, gid, items);
			root->right_offset = cuoset_erase(RIGHT(root), temp, gid, items) - items;
			root->size_right -= 1;
		}
	}
	if (root == NULL) return root;

	//root->height = 1 + max(height(LEFT(root)), height(RIGHT(root)));
	uint8_t hl = 0;
	if (HAS_LEFT(root)) hl = height(LEFT(root));
	uint8_t hr = 0;
	if (HAS_RIGHT(root)) hr = height(RIGHT(root));
	root->height = 1 + max(hl, hr);

	int8_t balance = getBalance(root, items);
	if (balance > 1) {
		int8_t bl = getBalance(LEFT(root), items);
		// Left Left case
		if (bl >= 0) {
			return rightRotate(root, items);
		}

		// Left Right case
		if (bl < 0) {
			//LEFT(root) = leftRotate(LEFT(root), items);
			root->left_offset = leftRotate(LEFT(root), items) - items;
			return rightRotate(root, items);
		}
	}

	if (balance < -1) {
		int8_t br = getBalance(RIGHT(root), items);
		// Right Right case
		if (br <= 0) {
			return leftRotate(root, items);
		}

		// Right Left case
		if (br > 0) {
			//RIGHT(root) = rightRotate(RIGHT(root), items);
			root->right_offset = rightRotate(RIGHT(root), items) - items;
			return leftRotate(root, items);
		}
	}

	return root;
}

/*
__device__ __host__ uint32_t cuoset_size(cuoset *s) {
	if (s == NULL) return 0;
	uint32_t size = 1+cuoset_size(LEFT(s))+cuoset_size(RIGHT(s));
	return size;
}
*/

__device__ cuoset* cuoset_get(cuoset* s, uint32_t p, cuoset *items) {
	while (s != NULL && s->in_use) {
		uint32_t size_l = s->size_left;
		if (p == size_l) {
			return s;
		} else if (p < size_l) {
			s = LEFT(s);
		} else {
			s = RIGHT(s);
			p = p-(size_l+1);
		}
	}
	return NULL;
}


/*
 * A simplified version of generating initial set.
 * A more secure way is to use the cache generation in eth.
 */
void generate_init_set(ordered_set_t& oset, uint64_t seed, uint32_t size) {
	std::uniform_int_distribution<uint64_t> dist(0, ULLONG_MAX);
	std::default_random_engine generator(seed);

	for (uint32_t i = 0; i < size; i++) {
		uint64_t v = dist(generator);
		oset.insert(v);
	}
}


__device__ cuoset *d_coset[MAX_WORKSIZE];

__host__ cuoset *h_qkc_hash_init(uint64_t *oset_raw, cuoset *items) {
	cuoset *coset = NULL;
	cuoset **unused = &(h_unused_item);
	h_oset_size = 0;
	for (int i = 0; i < INIT_SET_ENTRIES; i++) {
		*unused = &(items[i]);
		(*unused)->in_use = 0;
		coset = cuoset_insert(coset, oset_raw[i], 0, items);
	}
	//printf("Initialized on host. coset offset: %lu\n", coset-items);
	return coset;
}

__global__ void qkc_hash_init(uint64_t *oset_raw, cuoset *items_all) {
	uint32_t gid = blockIdx.x * blockDim.x + threadIdx.x;
	cuoset *coset = d_coset[gid];
	cuoset *items = items_all + gid*INIT_SET_ENTRIES;
	if (gid == 0) {
		cuoset **unused = &(unused_item[gid]);
		oset_size[gid] = 0;
		for (int i = 0; i < INIT_SET_ENTRIES; i++) {
			*unused = &(items[i]);
			(*unused)->in_use = 0;
			d_coset[0] = cuoset_insert(d_coset[0], oset_raw[i], gid, items);
		}
	}
}
__global__ void qkc_hash_init_copy(cuoset *items_all, uint16_t offset, uint32_t o_size) {
	uint32_t gid = blockIdx.x * blockDim.x + threadIdx.x;
	cuoset *items = items_all + gid*INIT_SET_ENTRIES;

	if (gid > 0) {
		for (int i = 0; i < INIT_SET_ENTRIES*sizeof(cuoset)/sizeof(uint64_t); i++) {
			uint64_t tmp = ((uint64_t*)(items_all))[i];
			((uint64_t*)(items))[i] = tmp;
		}
	}
	//uint16_t offset = d_coset[0] - items_all;
	d_coset[gid] = items + offset;
	//oset_size[gid] = oset_size[0];
	oset_size[gid] = o_size;
	unused_item[gid] = NULL;
}

#define swap64(x) \
	((uint64_t)((((uint64_t)(x)) >> 56) | \
		(((uint64_t)(x) & 0x00ff000000000000ULL) >> 40) | \
		(((uint64_t)(x) & 0x0000ff0000000000ULL) >> 24) | \
		(((uint64_t)(x) & 0x000000ff00000000ULL) >>  8) | \
		(((uint64_t)(x) & 0x00000000ff000000ULL) <<  8) | \
		(((uint64_t)(x) & 0x0000000000ff0000ULL) << 24) | \
		(((uint64_t)(x) & 0x000000000000ff00ULL) << 40) | \
		(((uint64_t)(x)) << 56)))

/*
 * QKC hash using ordered set.
 */
//#define DEBUG
#define MIX_SIZE 16
#define SEED_SIZE 8
#define RESULT_SIZE 4
__global__ void qkc_hash(
		uint64_t *result_out,
		cuoset *items_all,
		uint64_t *found,
		uint64_t *target,
		uint8_t *header,
		uint64_t start_nonce,
		uint8_t devid,
		uint32_t worksize) {
	uint32_t gid = blockIdx.x * blockDim.x + threadIdx.x;
	cuoset *coset = d_coset[gid];
	cuoset *items = items_all + gid*INIT_SET_ENTRIES;
#ifdef DEBUG
	if (gid == 0) {
		printf("Target %16lx %16lx %16lx %16lx\n", swap64(target[0]), swap64(target[1]), swap64(target[2]), swap64(target[3]));
	}
#endif
	
	/* Calculate SHA3_512 */
	uint64_t seed_hash[SEED_SIZE];

	{
		const int rsize = 72;
		const int rsize_byte = 9;
		uint64_t state[25];
		uint8_t temp[144];
		const uint32_t msglen = 40;
		memset(state, 0, sizeof(state));

		for (int i = 0; i < 4; i++) {
			state[i] = (((uint64_t*)header)[i]);
		}
		state[4] = (start_nonce) + gid;

#ifdef DEBUG
		if (gid == 10) {
			printf("CUDA sha3_512( ");
			for (int i = 0; i < 40; i++) {
				printf("%02x ", ((uint8_t*)state)[i]);
			}
			printf(" )\n");
		}
#endif

		// Padding
		memcpy(temp, state, msglen);
		memset(temp+msglen, 0, rsize-msglen);
		//temp[msglen] = 0x06;
		temp[msglen] = 0x01;
		temp[rsize - 1] |= 0x80;

		/* Absorb */
		for (int i = 0; i < rsize_byte; i++) {
			state[i] = ((uint64_t*)temp)[i];
		}
#ifdef DEBUG
		if (gid == 10) {
			printf("CUDA sha3_512 state1: ");
			for (int i = 0; i < rsize; i++) {
				printf("%02x ", ((uint8_t*)state)[i]);
			}
			printf("\n");
		}
#endif
		keccak_function(state);

		/* Squeeze */
		seed_hash[0] = state[0];
		seed_hash[1] = state[1];
		seed_hash[2] = state[2];
		seed_hash[3] = state[3];
		seed_hash[4] = state[4];
		seed_hash[5] = state[5];
		seed_hash[6] = state[6];
		seed_hash[7] = state[7];

#ifdef DEBUG
		if (gid == 10) {
			printf("CPU  Seed Hash: ");
			for (int i = 0; i < SEED_SIZE*8; i++) {
				printf("%02x ", ((uint8_t*)seed_init)[i]);
			}
			printf("\n");
			printf("CUDA Seed Hash: ");
			for (int i = 0; i < SEED_SIZE*8; i++) {
				printf("%02x ", ((uint8_t*)seed_hash)[i]);
			}
			printf("\n");
		}
#endif
	}

	uint64_t seed[SEED_SIZE];
	for (int i = 0; i < SEED_SIZE; i++) {
		//seed[i] = seed_init[i];
		seed[i] = seed_hash[i];
	}

	uint64_t mix[16];
	for (uint32_t i = 0; i < MIX_SIZE; i++) {
		mix[i] = seed[i % SEED_SIZE];
	}

	for (uint32_t i = 0; i < ACCESS_ROUND; i ++) {
		uint64_t new_data[16];
		uint64_t p = fnv64(i ^ seed[0], mix[i % MIX_SIZE]);
		for (uint32_t j = 0; j < MIX_SIZE; j++) {
			// Find the pth element and remove it
			cuoset *it = cuoset_get(coset, p % oset_size[gid], items);
			new_data[j] = it->value;
			coset = cuoset_erase(coset, it, gid, items);

			// Generate random data and insert it
			p = fnv64(p, new_data[j]);
			coset = cuoset_insert(coset, p, gid, items);

			// Find the next element index (ordered)
			p = fnv64(p, new_data[j]);
		}

		for (uint32_t j = 0; j < MIX_SIZE; j++) {
			mix[j] = fnv64(mix[j], new_data[j]);
		}
	}

	/*
	 * Compress
	 */
	uint64_t result[RESULT_SIZE];
	for (uint32_t i = 0; i < RESULT_SIZE; i++) {
		uint32_t j = i * 4;
	   	result[i] = fnv64(fnv64(fnv64(mix[j], mix[j + 1]), mix[j + 2]), mix[j + 3]);
	}


	/* Calculate SHA3_256 */
	uint64_t hash[4];

	{
		const int rsize = 136;
		const int rsize_byte = 17;
		uint64_t state[25];
		uint8_t temp[144];
		const uint32_t msglen = 96;
		memset(state, 0, sizeof(state));

		for (int i = 0; i < 8; i++) {
			state[i] = seed[i];
		}
		state[ 8] = result[0];
		state[ 9] = result[1];
		state[10] = result[2];
		state[11] = result[3];

		// Padding
		memcpy(temp, state, msglen);
		memset(temp+msglen, 0, rsize-msglen);
		temp[msglen] = 0x01;
		temp[rsize - 1] |= 0x80;

		/* Absorb */
		for (int i = 0; i < rsize_byte; i++) {
			state[i] = ((uint64_t*)temp)[i];
		}
		keccak_function(state);

		/* Squeeze */
		hash[0] = state[0];
		hash[1] = state[1];
		hash[2] = state[2];
		hash[3] = state[3];
	}

	if (swap64(hash[0]) <= swap64(target[0])) {
#ifdef DEBUG
		printf("%16lx < %16lx\n", swap64(hash[0]), swap64(target[0]));
		printf("CUDA Solve (devid: %d, gid: %d)!   ", devid, gid);
		for (int i = 0; i < 32; i++) {
			printf("%02x, ", ((uint8_t*)hash)[i]);
		}
		printf("\n");
		printf("CUDA Solve (devid: %d, gid: %d) Result: ", devid, gid);
		for (int i = 0; i < 32; i++) {
			printf("%02x, ", ((uint8_t*)result)[i]);
		}
		printf("\n");
		printf("CUDA Solve Seed Hash (devid: %d, gid: %d): ", devid, gid);
		for (int i = 0; i < SEED_SIZE*8; i++) {
			printf("%02x ", ((uint8_t*)seed)[i]);
		}
		printf("\n");
#endif
		if (!found[4]) {
			found[0] = result[0];
			found[1] = result[1];
			found[2] = result[2];
			found[3] = result[3];
			found[5] = gid + devid*worksize;
			found[4] = 1;
		}
	}
	//memcpy(result_out+gid*RESULT_SIZE, result, RESULT_SIZE*sizeof(uint64_t));
}

void qkc_hash_sorted_list(
		std::vector<uint64_t>& slist,
		std::array<uint64_t, 8>& seed,
		std::array<uint64_t, 4>& result) {
	std::array<uint64_t, 16> mix;
	for (uint32_t i = 0; i < mix.size(); i++) {
		mix[i] = seed[i % seed.size()];
	}

	for (uint32_t i = 0; i < ACCESS_ROUND; i ++) {
		std::array<uint64_t, 16> new_data;
		uint64_t p = fnv64(i ^ seed[0], mix[i % mix.size()]);
		for (uint32_t j = 0; j < mix.size(); j++) {
			// Find the pth element and remove it
			uint32_t idx = p % slist.size();
			new_data[j] = slist[idx];
			slist.erase(slist.begin() + idx);

			// Generate random data and insert it
			// if the vector doesn't contain it.
			p = fnv64(p, new_data[j]);
			auto it = std::lower_bound(slist.begin(), slist.end(), p);
			if (it == slist.end() || *it != p) {
				slist.insert(it, p);
			}
#ifdef DEBUG
			if (i == 60) {
				printf("access %d, mix %d: get value=%lu, insert value=%lu\n", i, j, new_data[j], p);
			}
#endif

			// Find the next element index (ordered)
			p = fnv64(p, new_data[j]);
		}

		for (uint32_t j = 0; j < mix.size(); j++) {
			mix[j] = fnv64(mix[j], new_data[j]);
		}
	}

	/*
	 * Compress
	 */
	for (uint32_t i = 0; i < result.size(); i++) {
		uint32_t j = i * 4;
		result[i] = fnv64(fnv64(fnv64(mix[j], mix[j + 1]), mix[j + 2]), mix[j + 3]);
	}
}


} // quarkchain
} // org


extern "C" void *cache_create(uint64_t *cache_ptr,
							  uint32_t cache_size) {
	ordered_set_t *oset = new ordered_set_t();
	for (uint32_t i = 0; i < cache_size; i++) {
		oset->insert(cache_ptr[i]);
	}
	return oset;
}

extern "C" void cache_destroy(void *ptr) {
	ordered_set_t *oset = (ordered_set_t *)ptr;
	delete oset;
}


bool device_init[64] = {};
uint64_t result0[6];
uint64_t *d_result0[64];
//uint64_t *d_seed_c[64];
org::quarkchain::cuoset *items[64];
//uint64_t *d_oset_raw[64];
uint64_t *found[64];
uint64_t *d_found[64];
uint64_t *d_target[64];
uint8_t *d_header[64];
cudaEvent_t kernelFinished[64];

int num_devices = 0;

extern "C" int32_t qkc_hash(void *cache_ptr,
			 //uint64_t* seed_ptr,
			 uint64_t* result_ptr,
			 uint64_t* target,
			 uint64_t* header,
			 uint64_t start_nonce,
			 uint32_t blocks,
			 uint32_t threads) {
	ordered_set_t *oset = (ordered_set_t *)cache_ptr;
	//printf("c start_nonce: %lu\n", start_nonce);

	checkCudaErrors(cudaGetDeviceCount(&num_devices));
	//ordered_set_t noset(*oset);*/

	//std::array<uint64_t, 8> seed;
	//std::array<uint64_t, 4> result;
	//std::copy(seed_ptr, seed_ptr + seed.size(), seed.begin());

	/*
	org::quarkchain::cuoset *coset = (org::quarkchain::cuoset *)malloc(sizeof(org::quarkchain::cuoset));
	org::quarkchain::cuoset *prev_item = coset;
	prev_item->value = *(oset->find_by_order(0));
	for (int i = 1; i < org::quarkchain::INIT_SET_ENTRIES; i++) {
		org::quarkchain::cuoset *item = (org::quarkchain::cuoset*)malloc(sizeof(org::quarkchain::cuoset));
		item->value = *(oset->find_by_order(i));
		prev_item->next = item;
		prev_item = item;
	}*/
	//org::quarkchain::qkc_hash<<<1,1>>>(coset, seed_ptr, result_ptr);

	//std::copy(result.begin(), result.end(), result_ptr);
	struct timeval tv1, tv2;
	gettimeofday(&tv1, NULL);

	uint64_t oset_raw[org::quarkchain::INIT_SET_ENTRIES];
	for (int i = 0; i < org::quarkchain::INIT_SET_ENTRIES; i++) {
		oset_raw[i] = *(oset->find_by_order(i));
	}

	// Prepare cuoset on host
	org::quarkchain::cuoset *h_items = (org::quarkchain::cuoset*)malloc(sizeof(org::quarkchain::cuoset)*org::quarkchain::INIT_SET_ENTRIES);
	org::quarkchain::cuoset *h_coset = org::quarkchain::h_qkc_hash_init(oset_raw, h_items);

	for (int i = 0; i < num_devices; i++) {
		cudaSetDevice(i);
		if (!device_init[i]) {
			checkCudaErrors(cudaMalloc(&d_result0[i], sizeof(uint64_t)*4*blocks*threads));
			checkCudaErrors(cudaMalloc(&items[i], sizeof(org::quarkchain::cuoset)*org::quarkchain::INIT_SET_ENTRIES*blocks*threads));
			checkCudaErrors(cudaMalloc(&d_target[i], sizeof(uint64_t)*4));
			checkCudaErrors(cudaMalloc(&d_header[i], sizeof(uint8_t)*32));
			//checkCudaErrors(cudaMalloc(&d_oset_raw[i], org::quarkchain::INIT_SET_ENTRIES*sizeof(uint64_t)));
			checkCudaErrors(cudaHostAlloc((void**)&(found[i]), sizeof(uint64_t)*6, cudaHostAllocMapped));
			checkCudaErrors(cudaHostGetDevicePointer((void**)&(d_found[i]), found[i], 0));

			cudaDeviceSetLimit(cudaLimitStackSize, 8192);
			size_t size_heap, size_stack;
			cudaDeviceGetLimit(&size_heap, cudaLimitMallocHeapSize);
			cudaDeviceGetLimit(&size_stack, cudaLimitStackSize);
			printf("Heap size found to be %d; Stack size found to be %d\n",(int)size_heap,(int)size_stack);

			checkCudaErrors(cudaEventCreate(&kernelFinished[i]));

			device_init[i] = true;
			printf("Initialized device %d\n", i);
		}
		for (int j = 0; j < 6; j++) {
			uint64_t *fo = found[i];
			fo[j] = 0;
		}

		checkCudaErrors(cudaMemcpy(d_target[i], target, sizeof(uint64_t)*4, cudaMemcpyHostToDevice));
		checkCudaErrors(cudaMemcpy(d_header[i], header, sizeof(uint8_t)*32, cudaMemcpyHostToDevice));

		// Copy cuoset to GPU
		checkCudaErrors(cudaMemcpy(items[i], h_items, sizeof(org::quarkchain::cuoset)*org::quarkchain::INIT_SET_ENTRIES, cudaMemcpyHostToDevice));
		org::quarkchain::qkc_hash_init_copy<<<blocks,threads>>>(items[i], h_coset-h_items, org::quarkchain::h_oset_size);

		// Calculate hashes
		org::quarkchain::qkc_hash<<<blocks,threads>>>(d_result0[i], items[i], d_found[i], d_target[i], d_header[i], start_nonce + i*blocks*threads, i, blocks*threads);
		checkCudaErrors(cudaEventRecord(kernelFinished[i]));
	}

	while (true) {
		usleep(10);
		uint8_t success = 0;
		for (int i = 0; i < num_devices; i++) {
			cudaSetDevice(i);
			
			if (cudaEventQuery(kernelFinished[i]) != cudaSuccess) {
				uint64_t *fo = found[i];
				if (fo[4] > 0) {
					printf("Found: ");
					for (int j = 0; j < 4; j++) {
						printf("%16lx ", fo[j]);
					}
					printf("\n");
					memcpy(result_ptr, fo, 6*sizeof(uint64_t));
					return num_devices * blocks * threads; // Early return when result found, to reduce orphans
					//break;
				}
			} else {
				success++;
			}
		}
		if (success >= num_devices) {
			// All GPUs completed
			break;
		}
	}

	for (int i = 0; i < num_devices; i++) {
		cudaSetDevice(i);

		checkCudaErrors(cudaDeviceSynchronize());
		uint64_t *fo = found[i];
		if (fo[4] > 0) {
			printf("Found: ");
			for (int j = 0; j < 4; j++) {
				printf("%16lx ", fo[j]);
			}
			printf("\n");
			memcpy(result_ptr, fo, 6*sizeof(uint64_t));
			return num_devices * blocks * threads; // Early return when result found, to reduce orphans
		}

		// Copy results
		checkCudaErrors(cudaDeviceSynchronize());
	}

	free(h_items);
	gettimeofday(&tv2, NULL);

	unsigned long utime1 = 1000000 * tv1.tv_sec + tv1.tv_usec;
	unsigned long utime2 = 1000000 * tv2.tv_sec + tv2.tv_usec;
	unsigned long udiff1 = utime2-utime1;

	double cudaseconds = udiff1 / 1000.0 / 1000.0;
	printf("Hashrate: %5.2f H/s\n", num_devices * blocks*threads / cudaseconds);

	return num_devices * blocks * threads;
}

void test_sorted_list(int blocks, int threads) {
	std::cout << "Testing sorted list implementation" << std::endl;
	ordered_set_t oset;

	org::quarkchain::generate_init_set(
		oset, 431, org::quarkchain::INIT_SET_ENTRIES);

	std::vector<uint64_t> slist;
	for (auto v : oset) {
		slist.push_back(v);
	}

	std::uniform_int_distribution<uint64_t> dist(0, ULLONG_MAX);
	std::default_random_engine generator(475);
	std::array<uint64_t, 8> seed;
	uint64_t seed_c[8];
	for (uint32_t j = 0; j < 8; j++) {
		seed[j] = dist(generator);
		seed_c[j] = seed[j];
	}

	//std::array<uint64_t, 4> result0;
	uint64_t result0[4];
	uint64_t *d_result0;
	uint64_t *d_seed_c;
	checkCudaErrors(cudaMalloc(&d_result0, sizeof(uint64_t)*4));
	checkCudaErrors(cudaMalloc(&d_seed_c, sizeof(uint64_t)*8));
	checkCudaErrors(cudaMemcpy(d_seed_c, seed_c, sizeof(uint64_t)*8, cudaMemcpyHostToDevice));
	org::quarkchain::cuoset *items;
	checkCudaErrors(cudaMalloc(&items, sizeof(org::quarkchain::cuoset)*org::quarkchain::INIT_SET_ENTRIES*blocks*threads));

	std::array<uint64_t, 4> result1;
	struct timeval tv1, tv2;
	gettimeofday(&tv1, NULL);
	org::quarkchain::qkc_hash_sorted_list(slist, seed, result1);
	gettimeofday(&tv2, NULL);
	/*org::quarkchain::cuoset *coset = (org::quarkchain::cuoset *)malloc(sizeof(org::quarkchain::cuoset));
	org::quarkchain::cuoset *prev_item = coset;
	prev_item->value = *(oset.find_by_order(0));*/
	uint64_t oset_raw[org::quarkchain::INIT_SET_ENTRIES];
	uint64_t *d_oset_raw;
	checkCudaErrors(cudaMalloc(&d_oset_raw, org::quarkchain::INIT_SET_ENTRIES*sizeof(uint64_t)));
	for (int i = 0; i < org::quarkchain::INIT_SET_ENTRIES; i++) {
		/*org::quarkchain::cuoset *item = (org::quarkchain::cuoset*)malloc(sizeof(org::quarkchain::cuoset));
		if (item == NULL) {
			printf("malloc failed, i=%d\n", i);
		}
		item->value = *(oset.find_by_order(i));
		item->next = NULL;
		prev_item->next = item;
		prev_item = item;
		//printf("Added item: %d, value: %lu\n", i, item->value);*/
		oset_raw[i] = *(oset.find_by_order(i));
	}
	checkCudaErrors(cudaMemcpy(d_oset_raw, oset_raw, sizeof(uint64_t)*org::quarkchain::INIT_SET_ENTRIES, cudaMemcpyHostToDevice));
	/*int count = 0;
	org::quarkchain::cuoset *iter = coset;
	for (; iter != NULL; iter = iter->next, count++);
	printf("elements in cuoset: %d\n", count);*/
	cudaDeviceSetLimit(cudaLimitStackSize, 8192);
	size_t size_heap, size_stack;
	cudaDeviceGetLimit(&size_heap, cudaLimitMallocHeapSize);
	cudaDeviceGetLimit(&size_stack, cudaLimitStackSize);
	printf("Heap size found to be %d; Stack size found to be %d\n",(int)size_heap,(int)size_stack);

	printf("Starting qkc_hash\n");
	struct timeval tv3, tv4, tv5, tv6, tv7;
	gettimeofday(&tv7, NULL);
	org::quarkchain::cuoset *h_items = (org::quarkchain::cuoset*)malloc(sizeof(org::quarkchain::cuoset)*org::quarkchain::INIT_SET_ENTRIES);
	org::quarkchain::cuoset *h_coset = org::quarkchain::h_qkc_hash_init(oset_raw, h_items);
	checkCudaErrors(cudaMemcpy(items, h_items, sizeof(org::quarkchain::cuoset)*org::quarkchain::INIT_SET_ENTRIES, cudaMemcpyHostToDevice));
	gettimeofday(&tv3, NULL);
	//org::quarkchain::qkc_hash_init<<<1,1>>>(d_oset_raw, items);
	//checkCudaErrors(cudaDeviceSynchronize());
	gettimeofday(&tv6, NULL);
	org::quarkchain::qkc_hash_init_copy<<<blocks,threads>>>(items, h_coset-h_items, org::quarkchain::h_oset_size);
	checkCudaErrors(cudaDeviceSynchronize());
	gettimeofday(&tv4, NULL);
	printf("Waiting for device synchronize\n");
	checkCudaErrors(cudaDeviceSynchronize());
	gettimeofday(&tv5, NULL);
	printf("Device synchronized\n");
	checkCudaErrors(cudaMemcpy(result0, d_result0, 4*sizeof(uint64_t), cudaMemcpyDeviceToHost));
	printf("result0 copied from device\n");
	free(h_items);

	unsigned long utime1 = 1000000 * tv1.tv_sec + tv1.tv_usec;
	unsigned long utime2 = 1000000 * tv2.tv_sec + tv2.tv_usec;
	unsigned long udiff1 = utime2-utime1;
	printf("CPU Sorted list Time: %lu us\n", udiff1);

	unsigned long utime3 = 1000000 * tv3.tv_sec + tv3.tv_usec;
	unsigned long utime4 = 1000000 * tv4.tv_sec + tv4.tv_usec;
	unsigned long utime5 = 1000000 * tv5.tv_sec + tv5.tv_usec;
	unsigned long utime6 = 1000000 * tv6.tv_sec + tv6.tv_usec;
	unsigned long utime7 = 1000000 * tv7.tv_sec + tv7.tv_usec;
	unsigned long cpuinit = utime3-utime7;
	unsigned long cudatime = utime5-utime3;
	unsigned long inittime = utime4-utime3;
	unsigned long init1time = utime6-utime3;
	printf("CPU Init1 Time: %lu us\n", cpuinit);
	printf("CUDA Init1 Time: %lu us\n", init1time);
	printf("CUDA Init Time: %lu us\n", inittime);
	printf("CUDA Time: %lu us\n", cudatime);

	double cudaseconds = cudatime / 1000 / 1000;
	printf("Hashrate: %5.2f H/s\n", blocks*threads / cudaseconds);

	for (uint32_t i = 0; i < result1.size(); i++) {
		if (result0[i] != result1[i]) {
			std::cout << "Test failed" << std::endl;
			return;
		}
	}
	std::cout << "Test passed" << std::endl;

}

void test_qkc_hash_perf() {
	ordered_set_t oset;

	auto t_start = std::chrono::steady_clock::now();
	org::quarkchain::generate_init_set(
		oset, 1, org::quarkchain::INIT_SET_ENTRIES);
	auto used_time = std::chrono::steady_clock::now() - t_start;
	std::cout << "Generate time: "
			  << std::chrono::duration<double, std::milli>(used_time).count()
			  << std::endl;

	t_start = std::chrono::steady_clock::now();
	ordered_set_t noset = oset;
	used_time = std::chrono::steady_clock::now() - t_start;
	std::cout << "Copy time: "
			  << std::chrono::duration<double, std::milli>(used_time).count()
			  << std::endl;

	std::uniform_int_distribution<uint64_t> dist(0, ULLONG_MAX);
	std::default_random_engine generator(475);

	t_start = std::chrono::steady_clock::now();
	uint32_t count = 1000;
	uint64_t seed[8];
	uint64_t result[8];
	for (uint32_t i = 0; i < count; i++) {
		for (uint32_t j = 0; j < 8; j++) {
			seed[j] = dist(generator);
		}

		ordered_set_t new_oset(oset);
		/*
		org::quarkchain::cuoset *coset = (org::quarkchain::cuoset *)malloc(sizeof(org::quarkchain::cuoset));
		org::quarkchain::cuoset *prev_item = coset;
		prev_item->value = *(new_oset.find_by_order(0));
		for (int i = 1; i < org::quarkchain::INIT_SET_ENTRIES; i++) {
			org::quarkchain::cuoset *item = (org::quarkchain::cuoset*)malloc(sizeof(org::quarkchain::cuoset));
			item->value = *(new_oset.find_by_order(i));
			prev_item->next = item;
			prev_item = item;
		}*/
		//org::quarkchain::qkc_hash<<<1,1>>>(coset, seed, result);
	}
	used_time = std::chrono::steady_clock::now() - t_start;
	std::cout << "Duration: "
		<< std::chrono::duration<double, std::milli>(used_time).count()
		<< std::endl;
}

void test_qkc_hash_slist_perf() {
	ordered_set_t oset;

	auto t_start = std::chrono::steady_clock::now();
	org::quarkchain::generate_init_set(
		oset, 1, org::quarkchain::INIT_SET_ENTRIES);
	auto used_time = std::chrono::steady_clock::now() - t_start;
	std::cout << "Generate time: "
			  << std::chrono::duration<double, std::milli>(used_time).count()
			  << std::endl;

	std::vector<uint64_t> slist;
	for (auto v : oset) {
		slist.push_back(v);
	}
	t_start = std::chrono::steady_clock::now();
	std::vector<uint64_t> nslist(slist);
	used_time = std::chrono::steady_clock::now() - t_start;
	std::cout << "Copy time: "
			  << std::chrono::duration<double, std::milli>(used_time).count()
			  << std::endl;

	std::uniform_int_distribution<uint64_t> dist(0, ULLONG_MAX);
	std::default_random_engine generator(475);

	t_start = std::chrono::steady_clock::now();
	uint32_t count = 1000;
	std::array<uint64_t, 8> seed;
	std::array<uint64_t, 4> result;
	for (uint32_t i = 0; i < count; i++) {
		for (uint32_t j = 0; j < 8; j++) {
			seed[j] = dist(generator);
		}

		std::vector<uint64_t> new_slist(slist);
		org::quarkchain::qkc_hash_sorted_list(new_slist, seed, result);
	}
	used_time = std::chrono::steady_clock::now() - t_start;
	std::cout << "Duration: "
			  << std::chrono::duration<double, std::milli>(used_time).count()
			  << std::endl;
}

int main(int argc, char** argv) {
	if (argc <= 1) {
		std::cout << "Must specify command in "
					 "qkc_perf, slist_test, slist_perf"
				  << std::endl;
		return -1;
	}

	if (strcmp(argv[1], "qkc_perf") == 0) {
		test_qkc_hash_perf();
	} else if (strcmp(argv[1], "slist_perf") == 0) {
		test_qkc_hash_slist_perf();
	} else if (strcmp(argv[1], "slist_test") == 0) {
		if (argc <= 3) {
			printf("Usage: %s slist_test <blocks> <threads>\n", argv[0]);
			return -1;
		}
		int blocks = atoi(argv[2]);
		int threads = atoi(argv[3]);
		test_sorted_list(blocks, threads);
	} else {
		std::cout << "Unrecognized command: " << argv[1] << std::endl;
		return -1;
	}

	return 0;
}
