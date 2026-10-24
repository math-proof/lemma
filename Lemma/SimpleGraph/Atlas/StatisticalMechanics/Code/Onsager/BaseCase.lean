import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.BaseCase
open StatMech StatMech.Onsager StatMech.Onsager.BaseCase


/--
[sum_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BaseCase.lean)
-/
@[path]
private lemma sum_shift_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4} :
-- imply
  (∑ i : Fin n, d (i + 1)) = ∑ i : Fin n, d i := by
-- proof
  apply StatMech.Onsager.BaseCase.sum_shift d

/--
[sum_turns_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BaseCase.lean)
-/
@[path]
private lemma sum_turns_zero_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4} :
-- imply
  (∑ i : Fin n, (d (i + 1) - d i)) = 0 := by
-- proof
  apply StatMech.Onsager.BaseCase.sum_turns_zero d

/--
[sum_turns_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BaseCase.lean)
-/
@[path]
private lemma sum_turns_eq_smul_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  (∑ i : Fin n, (d (i + 1) - d i)) = cc d • (1 : Fin 4) := by
-- proof
  apply StatMech.Onsager.BaseCase.sum_turns_eq_smul d hreflexfree

/--
[four_dvd_cc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BaseCase.lean)
-/
@[path]
private lemma four_dvd_cc_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  4 ∣ cc d := by
-- proof
  apply StatMech.Onsager.BaseCase.four_dvd_cc d hreflexfree

/--
[stepOf_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BaseCase.lean)
-/
@[path]
private lemma stepOf_ne_zero_eq
  {w : Fin 4} :
-- imply
  stepOf w ≠ 0 := by
-- proof
  apply StatMech.Onsager.BaseCase.stepOf_ne_zero w

/--
[cc_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BaseCase.lean)
-/
@[path]
private lemma cc_pos_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  0 < cc d := by
-- proof
  apply StatMech.Onsager.BaseCase.cc_pos d hclosed hreflexfree

/--
[four_le_cc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BaseCase.lean)
-/
@[path]
private lemma four_le_cc_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  4 ≤ cc d := by
-- proof
  apply StatMech.Onsager.BaseCase.four_le_cc d hclosed hreflexfree

/--
[base_cc_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BaseCase.lean)
-/
@[path]
private lemma base_cc_eq_four_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (hnodbl : Function.Injective (pos d) → cc d < 8) :
-- imply
  cc d = 4 := by
-- proof
  apply StatMech.Onsager.BaseCase.base_cc_eq_four d hclosed hsimple hreflexfree hnodbl


-- created on 2026-10-23
