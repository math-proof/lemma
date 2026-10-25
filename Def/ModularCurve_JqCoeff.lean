import Lemma.ModularCurve.X0

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

section JExpansion

variable (K : Type*) [CommRing K]

def jqModC : LaurentSeries K :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))

def jqNModC (N : ℕ) [NeZero N] : LaurentSeries K := qExpand K N (jqModC K)

end JExpansion

section FunctionField

variable (K : Type*) [Field K]

def modularFunctionFieldC (N : ℕ) [NeZero N] :
    IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K {jqModC K, jqNModC K N}

end FunctionField

end ModularCurve

end
