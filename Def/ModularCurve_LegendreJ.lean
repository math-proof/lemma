module

public import Mathlib

@[expose] public section

set_option autoImplicit false

namespace ModularCurve

def legendreJ {K : Type*} [Field K] (t : K) : K :=
  2 ^ 8 * (t ^ 2 - t + 1) ^ 3 / (t ^ 2 * (t - 1) ^ 2)

end ModularCurve
