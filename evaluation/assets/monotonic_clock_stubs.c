/* Measurement-only timer. No compiler transformation calls this function. */
#define _POSIX_C_SOURCE 200809L
#include <time.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/mlvalues.h>

CAMLprim value polcert_monotonic_clock(value unit)
{
  struct timespec now;
  (void)unit;
  if (clock_gettime(CLOCK_MONOTONIC, &now) != 0)
    caml_failwith("clock_gettime(CLOCK_MONOTONIC)");
  return caml_copy_double((double)now.tv_sec + (double)now.tv_nsec / 1e9);
}
