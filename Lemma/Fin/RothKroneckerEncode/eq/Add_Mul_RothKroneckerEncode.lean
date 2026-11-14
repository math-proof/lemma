import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothKroneckerEncode_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m D : ℕ}
  (i : Fin (m + 1) → ℕ) :
-- imply
  rothKroneckerEncode D i =
    i 0 + D * rothKroneckerEncode D (fun h ↦ i h.succ) := by
-- proof
  rw [rothKroneckerEncode, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, rothKroneckerEncode, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  simp [mul_left_comm, mul_comm]


-- updated on 2026-11-13
-- created on 2026-10-21
