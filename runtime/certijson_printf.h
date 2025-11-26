#ifndef CERTIJSON_PRINTF_H
#define CERTIJSON_PRINTF_H

#include <stdio.h>
#include <stdarg.h>

int cj_printf(const char* fmt, ...);
int cj_fprintf(FILE* stream, const char* fmt, ...);
int cj_sprintf(char* str, const char* fmt, ...);
int cj_snprintf(char* str, size_t size, const char* fmt, ...);

#endif
