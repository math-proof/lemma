import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothAuxCombination_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
  {m : ℕ}
  {r : Fin m → ℕ}
-- given
  (i : RothBox r)
  (c : RothCoeff r)
  (k : ℕ) :
-- imply
  (rothAuxCombination α i c).coeff k =
    ∑ j, (rothAuxTerm α i j).coeff k * c j := by
-- proof
  classical
  rw [rothAuxCombination, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.coeff_C_mul]
  ring


-- created on 2026-10-21
