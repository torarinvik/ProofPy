#include "certijson_io.h"
#include <string.h>

void cj_print_line(const char* s) {
    printf("%s\n", s);
}

void cj_print(const char* s) {
    printf("%s", s);
}

char* cj_read_line() {
    char* line = NULL;
    size_t len = 0;
    ssize_t read;

    read = getline(&line, &len, stdin);
    if (read != -1) {
        // Remove newline character if present
        if (line[read - 1] == '\n') {
            line[read - 1] = '\0';
        }
        return line;
    }
    return NULL;
}

char* cj_float_to_string(double f) {
    char* buffer = malloc(64); // Enough for double
    if (buffer) {
        snprintf(buffer, 64, "%f", f);
    }
    return buffer;
}

void print_point(struct Point p) {
    printf("Point(%d, %d)\n", p.x, p.y);
}

struct Point make_point(int x, int y) {
    struct Point p = {x, y};
    return p;
}

void DrawPixel(int x, int y, unsigned int color) {
    printf("DrawPixel(%d, %d, %08X)\n", x, y, color);
}
