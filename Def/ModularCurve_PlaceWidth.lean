import Lemma.ModularCurve.SupersingularNodePlaces
import Def.ModularCurve_JWidth
set_option Elab.async false
set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

def placeRamificationJ {K : Type*} [Field K] (N : ℕ) [NeZero N]
    (w : Place K (modularFunctionFieldC K N)) : ℕ :=
  (w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N)
    (w.evalAt (jGeomGen K N)))).toNat

def placeWidth {K : Type*} [Field K] [DecidableEq K] (N : ℕ) [NeZero N]
    (w : Place K (modularFunctionFieldC K N)) : ℕ :=
  jWidth (w.evalAt (jGeomGen K N)) / placeRamificationJ N w

end ModularCurve

end
