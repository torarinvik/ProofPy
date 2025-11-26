#ifndef CERTIJSON_ERRNO_H
#define CERTIJSON_ERRNO_H

#include <errno.h>

int cj_get_errno(void);
void cj_set_errno(int v);

#endif
