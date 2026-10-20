import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Matching.GaleShapley
open MathlibExt.Combinatorics.Matching.GaleShapley
open StrictTotalOrder


/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma ext_eq
  {T T' : StrictTotalOrder α}
-- given
  (h : T.lt = T'.lt) :
-- imply
  T = T' := by
-- proof
  apply MathlibExt.Combinatorics.Matching.GaleShapley.StrictTotalOrder.ext h

/--
[isBlockingPair_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma isBlockingPair_iff_eq
  {mp : MPrefs M W}
  {wp : WPrefs M W}
  {μ : PerfectMatching M W}
  {m : M}
  {w : W} :
-- imply
  IsBlockingPair mp wp μ m w ↔ (mp m).lt w (μ m) ∧ (wp w).lt m (μ.symm w) := by
-- proof
  apply MathlibExt.Combinatorics.Matching.GaleShapley.isBlockingPair_iff mp wp μ m w

/--
[isStable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma isStable_iff_eq
  {mp : MPrefs M W}
  {wp : WPrefs M W}
  {μ : PerfectMatching M W} :
-- imply
  IsStable mp wp μ ↔ ∀ m w, ¬ IsBlockingPair mp wp μ m w := by
-- proof
  apply MathlibExt.Combinatorics.Matching.GaleShapley.isStable_iff mp wp μ

/--
[gale_shapley_exists_stable_matching_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma gale_shapley_exists_stable_matching_general_eq
  [Fintype M] [Fintype W]
  {mp : MPrefs M W}
  {wp : WPrefs M W}
-- given
  (hCard : Fintype.card M = Fintype.card W) :
-- imply
  ∃ μ : PerfectMatching M W, IsStable mp wp μ := by
-- proof
  apply MathlibExt.Combinatorics.Matching.GaleShapley.gale_shapley_exists_stable_matching_general hCard mp wp

/--
[gale_shapley_exists_stable_matching](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma gale_shapley_exists_stable_matching_eq
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  {mp : MPrefs M W}
  {wp : WPrefs M W}
-- given
  (hCard : Fintype.card M = Fintype.card W) :
-- imply
  ∃ μ : PerfectMatching M W, IsStable mp wp μ := by
-- proof
  apply MathlibExt.Combinatorics.Matching.GaleShapley.gale_shapley_exists_stable_matching hCard mp wp


-- created on 2026-10-20
