#include "certijson_assert.h"
#include <stdio.h>
#include <stdlib.h>

void cj_assert(int condition, const char* message) {
    if (!condition) {
        if (message) {
            fprintf(stderr, "Assertion failed: %s\n", message);
        } else {
            fprintf(stderr, "Assertion failed\n");
        }
        abort();
    }
}
