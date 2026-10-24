import Mathlib
import Lemma.Fin.Sum_MulPowNeg1ValAdd.eq.Add_MulPowNeg1
open Fin


/--
[alternating_sum_eq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  {nn : ℕ}
  {a : Fin (nn + 1) → ℤ}
  {target : ℤ}
  {b : ℕ → ℤ}
-- given
  (hb0 : b 0 = target)
  (hbn : b (nn + 1) = 0)
  (hab : ∀ j : Fin (nn + 1), a j = b j.val + b (j.val + 1)) :
-- imply
  ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * a j = target := by
-- proof
  have : ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * a j =
      ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * (b j.val + b (j.val + 1)) := by
    congr 1
    ext j
    rw [hab j]
  rw [this, Sum_MulPowNeg1ValAdd.eq.Add_MulPowNeg1, hbn, mul_zero, add_zero, hb0]


-- created on 2026-10-24
