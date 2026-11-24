module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.NumberTheory.RothAuxiliary.Part3
public import Def.NumberTheory.RothAuxiliary.Part7
open MathlibExt.NumberTheory.RothAuxiliary


public section

/--
[rothAuxCombination_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
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


-- updated on 2026-11-13
-- created on 2026-10-21
