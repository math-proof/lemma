import Def.ModularCurve_PlaceWidth

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

def jWidthChar {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (j : K) : ℕ :=
  if q = 2 then (if j = 0 then 12 else 1)
  else if q = 3 then (if j = 0 then 6 else 1)
  else jWidth j

def placeWidthChar {K : Type*} [Field K] [DecidableEq K] (q N : ℕ) [NeZero N]
    (w : Place K (modularFunctionFieldC K N)) : ℕ :=
  jWidthChar q (w.evalAt (jGeomGen K N)) / placeRamificationJ N w

end ModularCurve

end
