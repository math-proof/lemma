import Mathlib
import Def.ModularCurve_LevelOneProlongationPair
import Def.ModularCurve_SmoothPointLocalRing

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


variable (R : LevelOneProlongationPair P)

theorem mem_smoothLocalRingFst_iff (v : Place k ↥(modularFunctionFieldC k 1)) (r : ↥(modularFunctionFieldBar (1 * q))) :
    r ∈ R.smoothLocalRingFst v ↔
      r ∈ R.R₁.integers ∧
        ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
          P.IsStrictTypeOne W → P.redFst W = v → r ∈ W.toValuationSubring := by
  simp only [smoothLocalRingFst, Subring.mem_inf, Subring.mem_iInf, Subtype.forall, and_imp]
  rfl

theorem mem_smoothLocalRingSnd_iff (v : Place k ↥(modularFunctionFieldC k 1)) (r : ↥(modularFunctionFieldBar (1 * q))) :
    r ∈ R.smoothLocalRingSnd v ↔
      r ∈ R.R₂.integers ∧
        ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
          P.IsStrictTypeTwo W → P.redSnd W = v → r ∈ W.toValuationSubring := by
  simp only [smoothLocalRingSnd, Subring.mem_inf, Subring.mem_iInf, Subtype.forall, and_imp]
  rfl

theorem mem_integers_of_mem_smoothLocalRingFst {v : Place k ↥(modularFunctionFieldC k 1)} {r : ↥(modularFunctionFieldBar (1 * q))}
    (h : r ∈ R.smoothLocalRingFst v) : r ∈ R.R₁.integers :=
  ((R.mem_smoothLocalRingFst_iff v r).mp h).1

theorem mem_integers_of_mem_smoothLocalRingSnd {v : Place k ↥(modularFunctionFieldC k 1)} {r : ↥(modularFunctionFieldBar (1 * q))}
    (h : r ∈ R.smoothLocalRingSnd v) : r ∈ R.R₂.integers :=
  ((R.mem_smoothLocalRingSnd_iff v r).mp h).1

theorem mem_toValuationSubring_of_mem_smoothLocalRingFst {v : Place k ↥(modularFunctionFieldC k 1)} {r : ↥(modularFunctionFieldBar (1 * q))}
    (h : r ∈ R.smoothLocalRingFst v) {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : P.IsStrictTypeOne W) (hv : P.redFst W = v) : r ∈ W.toValuationSubring :=
  ((R.mem_smoothLocalRingFst_iff v r).mp h).2 W hW hv

theorem mem_toValuationSubring_of_mem_smoothLocalRingSnd {v : Place k ↥(modularFunctionFieldC k 1)} {r : ↥(modularFunctionFieldBar (1 * q))}
    (h : r ∈ R.smoothLocalRingSnd v) {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : P.IsStrictTypeTwo W) (hv : P.redSnd W = v) : r ∈ W.toValuationSubring :=
  ((R.mem_smoothLocalRingSnd_iff v r).mp h).2 W hW hv

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end
