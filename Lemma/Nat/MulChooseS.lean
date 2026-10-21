import Mathlib
import sympy.Basic


/--
[roth_choose_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (l i j : ℕ) :
-- imply
  (l + j).choose j * (l + j + i).choose i =
    (i + j).choose i * (l + (i + j)).choose (i + j) := by
-- proof
  have h := Nat.choose_mul (n := l + j + i) (k := i + j) (s := i)
    (Nat.le_add_right i j)
  have hsub : l + j + i - i = l + j := by omega
  rw [hsub] at h
  have hk : i + j - i = j := by omega
  rw [hk] at h
  have htotal : l + j + i = l + (i + j) := by omega
  rw [htotal] at h
  rw [htotal]
  simpa only [mul_comm] using h.symm


-- created on 2026-10-21
