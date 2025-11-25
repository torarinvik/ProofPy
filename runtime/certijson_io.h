#ifndef CERTIJSON_IO_H
#define CERTIJSON_IO_H

#include <stdio.h>
#include <stdlib.h>

struct Point {
    int x;
    int y;
};

typedef struct Vector2 {
    float x;
    float y;
} Vector2;

void cj_print_line(const char* s);
void cj_print(const char* s);
char* cj_read_line();
char* cj_float_to_string(double f);
void print_point(struct Point p);
struct Point make_point(int x, int y);
void DrawPixel(int x, int y, unsigned int color);

#endif
