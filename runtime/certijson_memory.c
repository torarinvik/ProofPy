#include "certijson_memory.h"
#include <stdio.h>

uintptr_t cj_ptr_to_uintptr(const void* p) {
    return (uintptr_t)p;
}

void* cj_uintptr_to_ptr(uintptr_t v) {
    return (void*)v;
}

void* cj_ptr_offset(void* p, size_t bytes) {
    return (void*)((unsigned char*)p + bytes);
}

int32_t cj_load_int32(const void* p) {
    return *(const int32_t*)p;
}

int32_t cj_store_int32(void* p, int32_t v) {
    fprintf(stderr, "DEBUG: cj_store_int32 writing %d to %p\n", v, p);
    *(int32_t*)p = v;
    return v;
}

void cj_view_set_int32(void* view, int64_t idx, int32_t val) {
    int32_t* p = (int32_t*)view;
    p[idx] = val;
}

int32_t cj_view_get_int32(void* view, int64_t idx) {
    int32_t* p = (int32_t*)view;
    return p[idx];
}

int64_t cj_int32_to_int64(int32_t x) {
    return (int64_t)x;
}

void* cj_int64_to_ptr(int64_t v) {
    return (void*)v;
}

int64_t cj_ptr_to_int64(void* p) {
    return (int64_t)p;
}
