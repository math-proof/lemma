import Mathlib
import sympy.Basic
import Lemma.Nat.Add_1.le.Pow2.of.Gt_0
open Nat


/--
[roth_factorial_le_two_pow_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  k.factorial ≤ 2 ^ (k * k) := by
-- proof
  have hktwo : k ≤ 2 ^ k :=
    (Nat.le_add_right k 1).trans (Add_1.le.Pow2.of.Gt_0 hk)
  calc
    _ ≤ k ^ k := Nat.factorial_le_pow k
    _ ≤ (2 ^ k) ^ k := by gcongr
    _ = 2 ^ (k * k) := by rw [pow_mul]


-- created on 2026-10-21
