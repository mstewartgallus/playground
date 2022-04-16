#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Toy cuckoo hashing example.

I made this this morning while practising for an interview.

Probably really, really buggy and unfit for production use.
 */

struct cuck;

struct evict {
        bool found;
        char const *key;
        void *value;
};

struct cuck *cuck_new(void);
void cuck_delete(struct cuck *cuck);

struct evict cuck_put(struct cuck *cuck, char const *key, void *val);
void *cuck_get(struct cuck *cuck, char const *key);

static struct {
        char const *key;
        char const *val;
} keyvals[] = {
        { .key = "A", .val = "foo" },
        { .key = "B", .val = "bar" },
        { .key = "C", .val = "gizmo" },
        { .key = "D", .val = "baz" },
};

int main(int argc, char **argv)
{
        struct cuck *cuck = cuck_new();

        for (int ii = 0; ii < sizeof keyvals/sizeof keyvals[0]; ++ii) {
                char const *key = keyvals[ii].key;
                char const *val = keyvals[ii].val;

                struct evict evict = cuck_put(cuck, key, (void*)val);
                if (evict.found) {
                        /* TODO: rehash */
                        printf("collision! %s %s\n", key, val);
                        abort();
                }
        }

        for (int ii = 0; ii < sizeof keyvals/sizeof keyvals[0]; ++ii) {
                char const *key = keyvals[ii].key;
                char const *val = (char const *)cuck_get(cuck, key);

                printf("%s |-> %s\n", key, val);
        }

        cuck_delete(cuck);
        return 0;
}

/* FIXME: add a random offset at program init */
static size_t djb2(char const *str) {
        /* Daniel J. Berstein's hash function */
        /* http://www.cse.yorku.ca/~oz/hash.html */
        size_t index = 5381;
        for (int ii = 0; str[ii] != '\0'; ++ii) {
                index = (index * (size_t)33) ^ (size_t) str[ii];
        }
        return index;
}

static size_t sbdm(char const *str) {
        /* SBDM's hash function */
        /* http://www.cse.yorku.ca/~oz/hash.html */
        size_t index = 31;
        for (int ii = 0; str[ii] != '\0'; ++ii) {
                index = index * ((size_t)65599) + str[ii];
        }
        return index;
}

static size_t strhash(bool hash, char const *str) {
        return hash ? djb2(str) : sbdm(str);
}

struct hash;

struct lookup {
        bool found;
        void *value;
};

static struct hash *hash_new(size_t capacity);
static void hash_delete(struct hash *hash);

static struct evict hash1_put(struct hash *hash, char const *key, void *val);
static struct lookup hash1_get(struct hash *hash, char const *key);

static struct evict hash2_put(struct hash *hash, char const *key, void *val);
static struct lookup hash2_get(struct hash *hash, char const *key);

struct cuck {
        struct hash *restrict hash1;
        struct hash *restrict hash2;
};

enum { INITIAL_CAPACITY = 80 };
enum { MAX_EVICT = 8 };

struct cuck *cuck_new()
{
        struct cuck *ptr = malloc(sizeof *ptr);
        *ptr = (struct cuck) {
                .hash1 = hash_new(INITIAL_CAPACITY),
                .hash2 = hash_new(INITIAL_CAPACITY),
        };
        return ptr;
}

void cuck_delete(struct cuck *cuck)
{
        hash_delete(cuck->hash1);
        hash_delete(cuck->hash2);
        free(cuck);
}

struct evict cuck_put(struct cuck *cuck, char const *key, void *val)
{
        struct evict evict;

        for (int ii = 0; ii < MAX_EVICT; ++ii) {
                evict = hash1_put(cuck->hash1, key, val);
                if (!evict.found) {
                        return (struct evict){.found = false};
                }

                key = evict.key;
                val = evict.value;

                evict = hash2_put(cuck->hash2, key, val);
                if (!evict.found) {
                        return (struct evict){.found = false};
                }

                key = evict.key;
                val = evict.value;
        }

        return evict;
}

void *cuck_get(struct cuck *cuck, char const *key)
{
        struct lookup lookup;

        lookup = hash1_get(cuck->hash1, key);
        if (lookup.found) {
                return lookup.value;
        }
        lookup = hash2_get(cuck->hash2, key);
        if (lookup.found) {
                return lookup.value;
        }
        return 0;
}

struct hash {
        size_t capacity;

        char const **restrict keys;
        bool *restrict used;
        void **restrict value;
};

static struct hash *hash_new(size_t capacity)
{
        char const **keys = calloc(capacity, sizeof keys[0]);
        bool *used = calloc(capacity, sizeof used[0]);
        void **value = calloc(capacity, sizeof value[0]);

        struct hash *ptr = malloc(sizeof *ptr);
        *ptr = (struct hash) {
                .capacity = capacity,
                .keys = keys,
                .used = used,
                .value = value
        };
        return ptr;
}

static void hash_delete(struct hash *hash)
{
        free(hash);
}

static struct evict hash_put(bool n, struct hash *hash, char const *key, void *val);
static struct lookup hash_get(bool n, struct hash *hash, char const *key);

static struct evict hash1_put(struct hash *hash, char const *key, void *val)
{
        return hash_put(0, hash, key, val);
}

static struct lookup hash1_get(struct hash *hash, char const *key)
{
        return hash_get(0, hash, key);
}

static struct evict hash2_put(struct hash *hash, char const *key, void *val)
{
        return hash_put(1, hash, key, val);
}

static struct lookup hash2_get(struct hash *hash, char const *key)
{
        return hash_get(1, hash, key);
}

static struct evict hash_put(bool p, struct hash *hash, char const *key, void *val)
{
        size_t capacity = hash->capacity;
        size_t index = strhash(p, key) % capacity;

        if (hash->used[index]) {
                char const *old_key = hash->keys[index];
                if (strcmp(old_key, key) != 0) {
                        void *old = hash->value[index];
                        hash->value[index] = val;
                        return (struct evict) { .found = true, .key = old_key, .value = old };
                }
        }

        hash->used[index] = true;
        hash->keys[index] = key;
        hash->value[index] = val;
        return (struct evict) { .found = false };
}

static struct lookup hash_get(bool p, struct hash *hash, char const *key)
{
        size_t capacity = hash->capacity;
        size_t index = strhash(p, key) % capacity;

        if (!hash->used[index]) {
                return (struct lookup) {.found = false };
        }

        char const *old_key = hash->keys[index];
        if (strcmp(old_key, key) != 0) {
                return (struct lookup) {.found = false };
        }
        return (struct lookup) {
                .found = true,
                .value = hash->value[index] };
}
