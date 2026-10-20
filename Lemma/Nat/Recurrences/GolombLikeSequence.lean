import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.GolombLikeSequence
open MetaMathlibExt


/--
[golomb_like_closed_form](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma golomb_like_closed_form_eq
  {y z : ℤ}
-- given
  (hy : 2 ≤ y)
  (hz : 2 - y ≤ z)
  (hpar : y % 2 ≠ z % 2) :
-- imply
  (∃! f : ℕ+ → ℕ+,
    StrictMono f ∧
    (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2 ∧
    ∀ n : ℕ+,
    (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z) ∧
    ∀ f : ℕ+ → ℕ+,
    StrictMono f →
    (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2 →
    (∀ n : ℕ+,
    (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z) →
    ∀ k : ℕ, ∀ j : ℤ,
    -(((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k ≤ (j : ℚ) →
    (j : ℚ) < (((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k →
    ∃ m : ℕ+,
    (↑m.val : ℚ) =
    (((y : ℚ) + 1) * ((y : ℚ) + (z : ℚ) - 1) /
    (2 * ((y : ℚ) - 1))) *
    (y : ℚ) ^ k -
    (z : ℚ) / ((y : ℚ) - 1) + (j : ℚ) ∧
    (↑((f m).val) : ℚ) =
    (((y : ℚ) + (z : ℚ) - 1) / ((y : ℚ) - 1)) *
    (y : ℚ) ^ (k + 1) -
    (z : ℚ) / ((y : ℚ) - 1) +
    ((y : ℚ) + 1) * (j : ℚ) / 2 +
    ((y : ℚ) - 1) * |(j : ℚ)| / 2 := by
-- proof
  apply MetaMathlibExt.golomb_like_closed_form y z hy hz hpar


-- created on 2026-10-20
