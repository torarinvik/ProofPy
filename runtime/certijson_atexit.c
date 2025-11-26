#include <stdlib.h>
#include "certijson_atexit.h"

int cj_atexit(void (*cb)(void)) {
    return atexit(cb);
}
