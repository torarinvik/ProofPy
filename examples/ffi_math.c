#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <certijson_io.h>
#include <certijson_io.h>
#include <math.h>


int32_t main() {
cj_print_line("Calling sin(1.0)...");
cj_print_line(cj_float_to_string(sin(1.000000)));
return 0;
}

