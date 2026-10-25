import Mathlib

set_option autoImplicit false

namespace ModularCurve

def jWidth {K : Type*} [Field K] [DecidableEq K] (j : K) : ℕ :=
  if j = 0 then 3 else if j = 1728 then 2 else 1

end ModularCurve
