import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility
open MathlibExtTest MathlibExtTest.Combinatorics MathlibExtTest.Combinatorics.Enumerative MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility


namespace MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility

/--
[bernoulli_four_for_medianGenocchiOdd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MedianGenocchiDivisibility.lean)
-/
@[path]
lemma bernoulli_four_for_medianGenocchiOdd
-- imply
  bernoulli 4 = -1 / 30 := by
-- proof
  have h := sum_bernoulli 5
  simp only [show (5 : ℕ) = 4 + 1 from rfl, Finset.sum_range_succ] at h
  rw [bernoulli_zero, bernoulli_one, bernoulli_two] at h
  have h3 : bernoulli 3 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  rw [h3] at h
  have c2 : Nat.choose 5 2 = 10 := by decide
  rw [c2] at h
  norm_num at h ⊢
  linarith

end MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility

namespace MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility

/--
[bernoulli_six_for_medianGenocchiOdd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MedianGenocchiDivisibility.lean)
-/
@[path]
lemma bernoulli_six_for_medianGenocchiOdd
-- imply
  bernoulli 6 = 1 / 42 := by
-- proof
  have h := sum_bernoulli 7
  simp only [show (7 : ℕ) = 6 + 1 from rfl, Finset.sum_range_succ] at h
  rw [bernoulli_zero, bernoulli_one, bernoulli_two,
    bernoulli_four_for_medianGenocchiOdd] at h
  have h3 : bernoulli 3 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  have h5 : bernoulli 5 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  rw [h3, h5] at h
  have c2 : Nat.choose 7 2 = 21 := by decide
  have c4 : Nat.choose 7 4 = 35 := by decide
  rw [c2, c4] at h
  norm_num at h ⊢
  linarith

end MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility

namespace MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility

/--
[bernoulli_eight_for_medianGenocchiOdd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MedianGenocchiDivisibility.lean)
-/
@[path]
lemma bernoulli_eight_for_medianGenocchiOdd
-- imply
  bernoulli 8 = -1 / 30 := by
-- proof
  have h := sum_bernoulli 9
  simp only [show (9 : ℕ) = 8 + 1 from rfl, Finset.sum_range_succ] at h
  rw [bernoulli_zero, bernoulli_one, bernoulli_two,
    bernoulli_four_for_medianGenocchiOdd, bernoulli_six_for_medianGenocchiOdd] at h
  have h3 : bernoulli 3 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  have h5 : bernoulli 5 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  have h7 : bernoulli 7 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  rw [h3, h5, h7] at h
  have c2 : Nat.choose 9 2 = 36 := by decide
  have c4 : Nat.choose 9 4 = 126 := by decide
  have c6 : Nat.choose 9 6 = 84 := by decide
  rw [c2, c4, c6] at h
  norm_num at h ⊢
  linarith

end MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility

namespace MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility

/--
[medianGenocchiOdd_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MedianGenocchiDivisibility.lean)
-/
@[path]
lemma medianGenocchiOdd_four
-- imply
  MetaMathlibExt.medianGenocchiOdd 4 = 56 := by
-- proof
  have hg6 : MetaMathlibExt.genocchiNumberViaBernoulli 6 = -3 := by
    rw [MetaMathlibExt.genocchiNumberViaBernoulli,
      bernoulli_six_for_medianGenocchiOdd]
    norm_num
  have hg8 : MetaMathlibExt.genocchiNumberViaBernoulli 8 = 17 := by
    rw [MetaMathlibExt.genocchiNumberViaBernoulli,
      bernoulli_eight_for_medianGenocchiOdd]
    norm_num
  norm_num [MetaMathlibExt.medianGenocchiOdd, hg6, hg8,
    Finset.sum_range_succ]

end MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility


-- created on 2026-10-23
