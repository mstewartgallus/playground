#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Toy cuckoo hashing example.

I made this this morning while practising for an interview.

Probably really, really buggy and unfit for production use.
 */

struct table;

struct evict {
        bool found;
        char const *key;
        void *value;
};

enum rehashed { REHASHED, FAIL };

/*
  salt: see http://ocert.org/advisories/ocert-2011-003.html
 */
struct table *table_new(char const *salt, size_t capacity);
void table_delete(struct table *table);

struct evict table_put(struct table *table, char const *key, void *val);
void *table_get(struct table *table, char const *key);
enum rehashed table_copy(struct table const *table, struct table *new);

static struct {
        char const *key;
        char const *val;
} keyvals[] = {
        { .key = "A", .val = "foo" },
        { .key = "B", .val = "bar" },
        { .key = "C", .val = "gizmo" },
        { .key = "D", .val = "baz" },
};

enum { INITIAL_CAPACITY = 80 };

int main(int argc, char **argv)
{
        /* This should really be a random parameter */
        static char const salt[] = { "ASALT" };

        size_t capacity = INITIAL_CAPACITY;
        struct table *table = table_new(salt, capacity);

        for (int ii = 0; ii < sizeof keyvals/sizeof keyvals[0]; ++ii) {
                char const *key = keyvals[ii].key;
                char const *val = keyvals[ii].val;

                struct evict evict;
                for (;;) {
                        evict = table_put(table, key, (void*)val);
                        if (!evict.found) {
                                break;
                        }

                        /* FIXME infinite loop */
                        printf("collision! %s %s\n", key, val);

                        size_t new_capacity = 2 * capacity + 1;
                        struct table *new = table_new(salt, new_capacity);
                        if (table_copy(table, new) != REHASHED) {
                                puts("rehash failed");
                                abort();
                        }
                        table_delete(table);
                        table = new;
                        capacity = new_capacity;
                }
        }

        for (int ii = 0; ii < sizeof keyvals/sizeof keyvals[0]; ++ii) {
                char const *key = keyvals[ii].key;
                char const *val = (char const *)table_get(table, key);

                printf("%s |-> %s\n", key, val);
        }

        table_delete(table);
        return 0;
}

static size_t djb2_kernel(size_t state, char c) {
        return (state * (size_t)33) ^ (size_t) c;
}

static size_t sbdm_kernel(size_t state, char c) {
        return state * ((size_t)65599) + (size_t) c;
}

static size_t djb2(char const *salt, char const *str) {
        /* Daniel J. Berstein's hash function */
        /* http://www.cse.yorku.ca/~oz/hash.html */
        size_t state = 5381;

        for (int ii = 0; salt[ii] != '\0'; ++ii) {
                state = djb2_kernel(state, salt[ii]);
        }

        for (int ii = 0; str[ii] != '\0'; ++ii) {
                state = djb2_kernel(state, str[ii]);
        }

        return state;
}

static size_t sbdm(char const *salt, char const *str) {
        /* SBDM's hash function */
        /* http://www.cse.yorku.ca/~oz/hash.html */
        size_t state = 31;

        for (int ii = 0; salt[ii] != '\0'; ++ii) {
                state = sbdm_kernel(state, salt[ii]);
        }

        for (int ii = 0; str[ii] != '\0'; ++ii) {
                state = sbdm_kernel(state, str[ii]);
        }

        return state;
}

static size_t strhash(bool hash, char const *salt, char const *str) {
        return hash ? djb2(salt, str) : sbdm(salt, str);
}

struct hash;

struct lookup {
        bool found;
        void *value;
};

static struct hash *hash_new(char const *salt, size_t capacity);
static void hash_delete(struct hash *hash);

static enum rehashed hash_copy(struct hash const *hash, struct table *table);

static struct evict hash1_put(struct hash *hash, char const *key, void *val);
static struct lookup hash1_get(struct hash *hash, char const *key);

static struct evict hash2_put(struct hash *hash, char const *key, void *val);
static struct lookup hash2_get(struct hash *hash, char const *key);

struct table {
        struct hash *restrict hash1;
        struct hash *restrict hash2;
};

enum { MAX_EVICT = 8 };

struct table *table_new(char const *salt, size_t capacity)
{
        struct table *ptr = malloc(sizeof *ptr);
        *ptr = (struct table) {
                .hash1 = hash_new(salt, capacity),
                .hash2 = hash_new(salt, capacity),
        };
        return ptr;
}

void table_delete(struct table *table)
{
        hash_delete(table->hash1);
        hash_delete(table->hash2);
        free(table);
}

enum rehashed table_copy(struct table const *table, struct table *new)
{
        enum rehashed rehashed;

        rehashed = hash_copy(table->hash1, new);
        if (rehashed != REHASHED) {
                return rehashed;
        }

        rehashed = hash_copy(table->hash2, new);
        if (rehashed != REHASHED) {
                return rehashed;
        }

        return rehashed;
}

struct evict table_put(struct table *table, char const *key, void *val)
{
        struct evict evict;

        for (int ii = 0; ii < MAX_EVICT; ++ii) {
                evict = hash1_put(table->hash1, key, val);
                if (!evict.found) {
                        return (struct evict){.found = false};
                }

                key = evict.key;
                val = evict.value;

                evict = hash2_put(table->hash2, key, val);
                if (!evict.found) {
                        return (struct evict){.found = false};
                }

                key = evict.key;
                val = evict.value;
        }

        return evict;
}

void *table_get(struct table *table, char const *key)
{
        struct lookup lookup;

        lookup = hash1_get(table->hash1, key);
        if (lookup.found) {
                return lookup.value;
        }
        lookup = hash2_get(table->hash2, key);
        if (lookup.found) {
                return lookup.value;
        }
        return 0;
}

struct hash {
        char const *salt;
        size_t capacity;

        char const **restrict keys;
        bool *restrict used;
        void **restrict value;
};

static struct hash *hash_new(char const *salt, size_t capacity)
{
        char const **keys = calloc(capacity, sizeof keys[0]);
        bool *used = calloc(capacity, sizeof used[0]);
        void **value = calloc(capacity, sizeof value[0]);

        struct hash *ptr = malloc(sizeof *ptr);
        *ptr = (struct hash) {
                .salt = salt,
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

static enum rehashed hash_copy(struct hash const *hash, struct table *table)
{
        /* assume if it's time to rehash we have a decent load factor,
         * say 0.5 so it's okay to iterate over everything */

        size_t capacity = hash->capacity;

        for (size_t ii = 0; ii < capacity; ++ii) {
                if (!hash->used[ii]) {
                        continue;
                }

                char const *key = hash->keys[ii];
                void *val = hash->value[ii];

                struct evict evict = table_put(table, key, val);
                if (evict.found) {
                        /* FIXME: not sure how to handle collisions
                         * during rehashing */
                        return FAIL;
                }
        }

        return REHASHED;
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
        char const *salt = hash->salt;
        size_t index = strhash(p, salt, key) % capacity;

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
        char const *salt = hash->salt;
        size_t index = strhash(p, salt, key) % capacity;

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
