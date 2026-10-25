import Mathlib
import Structure.ModularCurve_ProlongationTuple
import Structure.IncidenceSystem

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

noncomputable abbrev jNFun (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_mul_right N q))⟩

noncomputable abbrev jNQFun (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_refl (N * q)))⟩

end ModularCurve.PlaceSpecialization
