// RUN: %cladclang %s -I%S/../../include -Xclang -verify -c

#include "clad/Differentiator/Differentiator.h"

double fn_dangling_checkpoint(double x, double y) {
  #pragma clad checkpoint loop  // expected-error {{'#pragma clad checkpoint loop' is only allowed before a loop}}
  return x + 1;
}

double fn_mixed_checkpoint(double x, double y) {
  #pragma clad checkpoint loop
  for (int i = 0; i < 2; ++i)
    x += y;

  #pragma clad checkpoint loop  // expected-error {{'#pragma clad checkpoint loop' is only allowed before a loop}}
  return x;
}

double fn_nested_checkpoint(double x, double y) {
  double sum = 0;
  // Re-executing a transformed nested loop would advance its counter without
  // its reverse sweep consuming it, so the pragma is ignored.
  #pragma clad checkpoint loop  // expected-warning {{'#pragma clad checkpoint loop' ignored because the loop contains a nested loop; values will be stored instead}}
  for (int i = 0; i < 2; ++i)
    for (int j = 0; j < 2; ++j)
      sum += x * y;
  return sum;
}

double fn_ptr_write_checkpoint(double x) {
  double storage[2] = {0, 0};
  double* p = storage;
  // A replay cannot restore state written through a pointer.
  #pragma clad checkpoint loop  // expected-warning {{'#pragma clad checkpoint loop' ignored because the loop writes through a pointer, array, or member that is not local to the loop; values will be stored instead}}
  for (int i = 0; i < 2; ++i)
    p[i] = x * i;
  return p[0] + p[1];
}

int main() {
  // Hits duplicate pragma-diagnosis suppression path.
  clad::gradient(fn_dangling_checkpoint);
  clad::hessian(fn_dangling_checkpoint, "x");

  // Hits reverse loop checkpoint scan with one invalid entry in map.
  clad::gradient(fn_mixed_checkpoint);

  // Unsupported loops fall back to storing values, with a warning.
  clad::gradient(fn_nested_checkpoint);
  clad::gradient(fn_ptr_write_checkpoint);
}
