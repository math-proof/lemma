import Def.ModularCurve_ProlongationTuple

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve

namespace ModularCurve

namespace PlaceSpecialization

namespace ProlongationTuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

def smoothLocalRingFst (R : ProlongationTuple P) (v : Place k (modularFunctionFieldC k N)) :
    Subring (modularFunctionFieldBar (N * q)) :=
  R.R₁.integers.toSubring ⊓
    ⨅ W : {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) //
            P.IsStrictFst W ∧ P.reduceFst W = v},
      (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).toValuationSubring.toSubring

def smoothLocalRingSnd (R : ProlongationTuple P) (v : Place k (modularFunctionFieldC k N)) :
    Subring (modularFunctionFieldBar (N * q)) :=
  R.R₂.integers.toSubring ⊓
    ⨅ W : {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) //
            P.IsStrictSnd W ∧ P.reduceSnd W = v},
      (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).toValuationSubring.toSubring

end ProlongationTuple

end PlaceSpecialization

end ModularCurve

end
