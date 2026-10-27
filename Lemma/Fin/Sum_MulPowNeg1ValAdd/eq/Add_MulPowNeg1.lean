import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[alternating_sum_general'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  {nn : ℕ}
  {b : ℕ → ℤ} :
-- imply
  ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * (b j.val + b (j.val + 1)) =
    b 0 + (-1 : ℤ) ^ nn * b (nn + 1) := by
-- proof
  induction nn with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring


-- created on 2026-10-24
