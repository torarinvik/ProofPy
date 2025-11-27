#ifndef CERTIJSON_IO_H
#define CERTIJSON_IO_H

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

struct Point {
    int x;
    int y;
};

void cj_print_line(const char* s);
void cj_print(const char* s);
char* cj_read_line();
char* cj_float_to_string(double f);
void print_point(struct Point p);
struct Point make_point(int x, int y);

// Debug helpers
void cj_debug_int(const char* label, int32_t value);
void cj_debug_bool(const char* label, bool value);

#endif
