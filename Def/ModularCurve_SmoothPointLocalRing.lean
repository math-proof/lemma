import Mathlib
import Structure.ModularCurve_LevelOneProlongationPair

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

namespace LevelOneProlongationPair

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

def smoothLocalRingFst (R : LevelOneProlongationPair P) (v : Place k ↥(modularFunctionFieldC k 1)) :
    Subring ↥(modularFunctionFieldBar (1 * q)) :=
  R.R₁.integers.toSubring ⊓
    ⨅ W : {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) //
            P.IsStrictTypeOne W ∧ P.redFst W = v},
      (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).toValuationSubring.toSubring

def smoothLocalRingSnd (R : LevelOneProlongationPair P) (v : Place k ↥(modularFunctionFieldC k 1)) :
    Subring ↥(modularFunctionFieldBar (1 * q)) :=
  R.R₂.integers.toSubring ⊓
    ⨅ W : {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) //
            P.IsStrictTypeTwo W ∧ P.redSnd W = v},
      (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).toValuationSubring.toSubring

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end
