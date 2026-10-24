import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.WalkCellClose
open StatMech StatMech.Onsager StatMech.Onsager.WalkCellClose


/--
[base_cc_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellClose.lean)
-/
@[path]
private lemma base_cc_eq_four_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cc d = 4 := by
-- proof
  apply StatMech.Onsager.WalkCellClose.base_cc_eq_four d hclosed hsimple hreflexfree

/--
[cc_lt_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellClose.lean)
-/
@[path]
private lemma cc_lt_eight_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cc d < 8 := by
-- proof
  apply StatMech.Onsager.WalkCellClose.cc_lt_eight d hclosed hsimple hreflexfree

/--
[base_cc_eq_four'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellClose.lean)
-/
@[path]
private lemma base_cc_eq_four'_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cc d = 4 := by
-- proof
  apply StatMech.Onsager.WalkCellClose.base_cc_eq_four' d hclosed hsimple hreflexfree

/--
[cc_lt_eight'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellClose.lean)
-/
@[path]
private lemma cc_lt_eight'_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cc d < 8 := by
-- proof
  apply StatMech.Onsager.WalkCellClose.cc_lt_eight' d hclosed hsimple hreflexfree


-- created on 2026-10-23
