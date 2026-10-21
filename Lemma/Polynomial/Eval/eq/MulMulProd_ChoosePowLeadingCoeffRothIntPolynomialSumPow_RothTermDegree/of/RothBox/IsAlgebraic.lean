import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.Eval.eq.MulPowS.of.Le.IsAlgebraic
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothAuxTerm_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
  {m : ℕ}
  {r : Fin m → ℕ}
-- given
  (hα : IsAlgebraic ℚ α)
  (i j : RothBox r) :
-- imply
  eval₂ (algebraMap ℤ ℝ)
    (((rothIntPolynomial α).leadingCoeff : ℝ) * α)
    (rothAuxTerm α i j) =
    (∏ h, (Nat.choose (j h) (i h) : ℝ)) *
      ((rothIntPolynomial α).leadingCoeff : ℝ) ^ (∑ h, r h) *
        α ^ rothTermDegree i j := by
-- proof
  let S := ∑ h, r h
  have hn : rothTermDegree i j ≤ S := by
    dsimp [S]
    unfold rothTermDegree
    gcongr with h
    exact (Nat.sub_le _ _).trans (Nat.le_of_lt_succ (j h).isLt)
  rw [rothAuxTerm, eval₂_mul, eval₂_C,
    Eval.eq.MulPowS.of.Le.IsAlgebraic α hn hα]
  rw [map_prod]
  rw [algebraMap_int_eq, Int.coe_castRingHom]
  dsimp only
  simp only [Int.cast_natCast]
  dsimp [S]
  ring


-- created on 2026-10-21
