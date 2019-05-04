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

using namespace std;
using namespace __gnu_pbds;

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

typedef struct cuoset {
	struct cuoset *next;
	uint64_t value;
} cuoset;

__host__ cuoset* cuoset_get(cuoset* s, uint32_t p) {
	cuoset *iter = s;
	for (int i = 0; i < p; i++) {
		iter = iter->next;
		if (iter == NULL) {
			printf("cuoset_get iter==NULL, shouldn't happen.. i=%d, p=%d\n", i, p);
			return NULL;
		}
	}
	return iter;
}

cuoset *unused_item = NULL;
uint32_t oset_size = INIT_SET_ENTRIES;
__host__ cuoset *cuoset_insert(cuoset *s, uint64_t value) {
	//printf("inserting %lu\n", value);
	if (s == NULL) {
		printf("s==NULL\n");
		return s;
	}
	if (unused_item != NULL) {
		unused_item->value = value;
		if (value < s->value) {
			unused_item->next = s;
			oset_size++;
			return unused_item;
		}
		for (cuoset *iter = s; iter != NULL; iter = iter->next) {
			if (value == iter->value) {
				//printf("Value already in set, not inserting\n");
				return s;
			}
			if (value > iter->value) {
				if (iter->next == NULL) {
					iter->next = unused_item;
					oset_size++;
					return s;
				} else if (value < iter->next->value) {
					unused_item->next = iter->next;
					iter->next = unused_item;
					oset_size++;
					return s;
				}
			}
		}
	}
	printf("unusude item == NULL\n");
	printf("Unhandled insert!\n");
	return s;
}

__host__ cuoset *cuoset_erase(cuoset *s, cuoset *item) {
	//printf("erasing %lu\n", item->value);
	oset_size--;
	cuoset *next = item->next;
	unused_item = item;
	unused_item->next = NULL;
	if (s == item) {
		//printf("erasing first position..\n");
		if (next == NULL) {
			printf(">next is null, bad idea..\n");
		}
		return next;
	}
	cuoset *iter = s;
	for (; iter != NULL; iter = iter->next) {
		if (iter->next == item) {
			iter->next = next;
			break;
		}
	}
	return s;
}

void cuoset_print(cuoset *s) {
	printf("[ ");
	for (cuoset *iter = s; iter != NULL; iter = iter->next) {
		printf("%lu ", iter->value);
	}
	printf("]\n");
}

void cuoset_test() {
	printf("cuoset_test\n");
	cuoset *oset = (cuoset*)malloc(sizeof(cuoset));
	oset->value = 0;
	cuoset *prev_item = oset;
	for (int i = 1; i < 10; i++) {
		cuoset *item = (cuoset*)malloc(sizeof(cuoset));
		item->value = i;
		prev_item->next = item;
		prev_item = item;
	}

	cuoset_print(oset);

	cuoset *item = cuoset_get(oset, 5);
	oset = cuoset_erase(oset, item);
	oset = cuoset_insert(oset, 5);
	cuoset_print(oset);

	item = cuoset_get(oset, 0);
	oset = cuoset_erase(oset, item);
	oset = cuoset_insert(oset, 0);
	cuoset_print(oset);

	item = cuoset_get(oset, 9);
	oset = cuoset_erase(oset, item);
	oset = cuoset_insert(oset, 9);
	cuoset_print(oset);

	item = cuoset_get(oset, 4);
	oset = cuoset_erase(oset, item);
	oset = cuoset_insert(oset, 5);
	cuoset_print(oset);

	item = cuoset_get(oset, 5);
	oset = cuoset_erase(oset, item);
	oset = cuoset_insert(oset, 3);
	cuoset_print(oset);

	item = cuoset_get(oset, 3);
	oset = cuoset_erase(oset, item);
	oset = cuoset_insert(oset, 4);
	cuoset_print(oset);
}

void oset_print(ordered_set_t *s) {
	printf("[ ");
	for (int i = 0; i < s->size(); i++) {
		printf("%lu ", *(s->find_by_order(i)));
	}
	printf("]\n");
}

void oset_test() {
	printf("oset_test\n");
    ordered_set_t *oset = new ordered_set_t();
	for (int i = 0; i < 10; i++) {
		oset->insert(i);
	}

	oset_print(oset);

	auto item = oset->find_by_order(5);
	oset->erase(item);
	oset->insert(5);
	oset_print(oset);

	item = oset->find_by_order(0);
	oset->erase(item);
	oset->insert(0);
	oset_print(oset);

	item = oset->find_by_order(9);
	oset->erase(item);
	oset->insert(9);
	oset_print(oset);

	item = oset->find_by_order(4);
	oset->erase(item);
	oset->insert(5);
	oset_print(oset);

	item = oset->find_by_order(5);
	oset->erase(item);
	oset->insert(3);
	oset_print(oset);

	item = oset->find_by_order(3);
	oset->erase(item);
	oset->insert(4);
	oset_print(oset);

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

/*
 * QKC hash using ordered set.
 */
#define MIX_SIZE 16
#define SEED_SIZE 8
#define RESULT_SIZE 4
__host__ void qkc_hash(
        cuoset *oset,
		uint64_t *seed,
		uint64_t *result) {
	uint64_t mix[16];
    for (uint32_t i = 0; i < MIX_SIZE; i++) {
        mix[i] = seed[i % SEED_SIZE];
    }

    for (uint32_t i = 0; i < ACCESS_ROUND; i ++) {
		uint64_t new_data[16];
        uint64_t p = fnv64(i ^ seed[0], mix[i % MIX_SIZE]);
        for (uint32_t j = 0; j < MIX_SIZE; j++) {
            // Find the pth element and remove it
            cuoset *it = cuoset_get(oset, p % oset_size);
            new_data[j] = it->value;
            oset = cuoset_erase(oset, it);

            // Generate random data and insert it
            p = fnv64(p, new_data[j]);
            oset = cuoset_insert(oset, p);

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
    for (uint32_t i = 0; i < RESULT_SIZE; i++) {
        uint32_t j = i * 4;
        result[i] = fnv64(fnv64(fnv64(mix[j], mix[j + 1]), mix[j + 2]), mix[j + 3]);
    }
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

extern "C" void qkc_hash(void *cache_ptr,
                         uint64_t* seed_ptr,
                         uint64_t* result_ptr) {
    ordered_set_t *oset = (ordered_set_t *)cache_ptr;
    ordered_set_t noset(*oset);

    //std::array<uint64_t, 8> seed;
    //std::array<uint64_t, 4> result;
    //std::copy(seed_ptr, seed_ptr + seed.size(), seed.begin());

	org::quarkchain::cuoset *coset = (org::quarkchain::cuoset *)malloc(sizeof(org::quarkchain::cuoset));
	org::quarkchain::cuoset *prev_item = coset;
	prev_item->value = *(oset->find_by_order(0));
	for (int i = 1; i < org::quarkchain::INIT_SET_ENTRIES; i++) {
		org::quarkchain::cuoset *item = (org::quarkchain::cuoset*)malloc(sizeof(org::quarkchain::cuoset));
		item->value = *(oset->find_by_order(i));
		prev_item->next = item;
		prev_item = item;
	}
    org::quarkchain::qkc_hash(coset, seed_ptr, result_ptr);

    //std::copy(result.begin(), result.end(), result_ptr);
}

void test_sorted_list() {
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
    std::array<uint64_t, 4> result1;
	org::quarkchain::cuoset *coset = (org::quarkchain::cuoset *)malloc(sizeof(org::quarkchain::cuoset));
	org::quarkchain::cuoset *prev_item = coset;
	prev_item->value = *(oset.find_by_order(0));
	for (int i = 1; i < org::quarkchain::INIT_SET_ENTRIES; i++) {
		org::quarkchain::cuoset *item = (org::quarkchain::cuoset*)malloc(sizeof(org::quarkchain::cuoset));
		if (item == NULL) {
			printf("malloc failed, i=%d\n", i);
		}
		item->value = *(oset.find_by_order(i));
		item->next = NULL;
		prev_item->next = item;
		prev_item = item;
		//printf("Added item: %d, value: %lu\n", i, item->value);
	}
	int count = 0;
	org::quarkchain::cuoset *iter = coset;
	for (; iter != NULL; iter = iter->next, count++);
	printf("elements in cuoset: %d\n", count);
    org::quarkchain::qkc_hash(coset, seed_c, result0);
    org::quarkchain::qkc_hash_sorted_list(slist, seed, result1);

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
		org::quarkchain::cuoset *coset = (org::quarkchain::cuoset *)malloc(sizeof(org::quarkchain::cuoset));
		org::quarkchain::cuoset *prev_item = coset;
		prev_item->value = *(new_oset.find_by_order(0));
		for (int i = 1; i < org::quarkchain::INIT_SET_ENTRIES; i++) {
			org::quarkchain::cuoset *item = (org::quarkchain::cuoset*)malloc(sizeof(org::quarkchain::cuoset));
			item->value = *(new_oset.find_by_order(i));
			prev_item->next = item;
			prev_item = item;
		}
		org::quarkchain::qkc_hash(coset, seed, result);
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
        test_sorted_list();
    } else if (strcmp(argv[1], "cuoset_test") == 0) {
		org::quarkchain::cuoset_test();
		org::quarkchain::oset_test();
    } else {
        std::cout << "Unrecognized command: " << argv[1] << std::endl;
        return -1;
    }

    return 0;
}
