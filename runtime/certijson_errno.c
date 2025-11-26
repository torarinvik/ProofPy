#include "certijson_errno.h"

int cj_get_errno(void) {
    return errno;
}

void cj_set_errno(int v) {
    errno = v;
}
