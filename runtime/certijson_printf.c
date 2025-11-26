#include "certijson_printf.h"
#include <string.h>

int cj_printf(const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    int r = vprintf(fmt, args);
    va_end(args);
    return r;
}

int cj_fprintf(FILE* stream, const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    int r = vfprintf(stream, fmt, args);
    va_end(args);
    return r;
}

int cj_sprintf(char* str, const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    int r = vsprintf(str, fmt, args);
    va_end(args);
    return r;
}

int cj_snprintf(char* str, size_t size, const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    int r = vsnprintf(str, size, fmt, args);
    va_end(args);
    return r;
}
