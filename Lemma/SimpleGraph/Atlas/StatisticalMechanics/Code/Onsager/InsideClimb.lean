import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.InsideClimb
open StatMech StatMech.Onsager StatMech.Onsager.InsideClimb


/--
[inside_climb_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean)
-/
@[path]
private lemma inside_climb_x_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hinside : rayParity d a b = 1)
  (hstr : ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = a + 1 → ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧ b < max ((pos d k).2) ((pos d (k + 1)).2))) :
-- imply
  rayParity d (a + 1) b = 1 := by
-- proof
  apply StatMech.Onsager.InsideClimb.inside_climb_x d hclosed a b hinside hstr

/--
[inside_climb_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean)
-/
@[path]
private lemma inside_climb_y_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hinside : rayParity d a b = 1)
  (h : ∀ k : Fin n, isHorizEdge (d k) → min ((pos d k).1) ((pos d (k + 1)).1) = a → (pos d k).2 ≠ b + 1) :
-- imply
  rayParity d a (b + 1) = 1 := by
-- proof
  apply StatMech.Onsager.InsideClimb.inside_climb_y d a b hinside h

/--
[nw_corner_coords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean)
-/
@[path]
private lemma nw_corner_coords_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hN : d i = 1)
  (hW : d (i + 1) = 2) :
-- imply
  pos d i = ((pos d (i + 1)).1, (pos d (i + 1)).2 - 1) ∧ pos d (i + 1 + 1) = ((pos d (i + 1)).1 - 1, (pos d (i + 1)).2) := by
-- proof
  apply StatMech.Onsager.InsideClimb.nw_corner_coords d hclosed i hN hW

/--
[nw_corner_not_climbable_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean)
-/
@[path]
private lemma nw_corner_not_climbable_x_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hN : d i = 1)
  (hW : d (i + 1) = 2) :
-- imply
  ¬ (∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = ((pos d (i + 1)).1 - 1) + 1 → ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ (pos d (i + 1)).2 - 1 ∧ (pos d (i + 1)).2 - 1 < max ((pos d k).2) ((pos d (k + 1)).2))) := by
-- proof
  apply StatMech.Onsager.InsideClimb.nw_corner_not_climbable_x d hclosed i hN hW

/--
[nw_corner_not_climbable_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean)
-/
@[path]
private lemma nw_corner_not_climbable_y_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hN : d i = 1)
  (hW : d (i + 1) = 2) :
-- imply
  ¬ (∀ k : Fin n, isHorizEdge (d k) → min ((pos d k).1) ((pos d (k + 1)).1) = (pos d (i + 1)).1 - 1 → (pos d k).2 ≠ ((pos d (i + 1)).2 - 1) + 1) := by
-- proof
  apply StatMech.Onsager.InsideClimb.nw_corner_not_climbable_y d hclosed i hN hW

/--
[lexmax_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean)
-/
@[path]
private lemma lexmax_unique_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M M' : Fin n}
-- given
  (hsimple : Function.Injective (pos d))
  (hM : ∀ j : Fin n, toLex (pos d j) ≤ toLex (pos d M))
  (hM' : ∀ j : Fin n, toLex (pos d j) ≤ toLex (pos d M')) :
-- imply
  M = M' := by
-- proof
  apply StatMech.Onsager.InsideClimb.lexmax_unique d hsimple hM hM'

/--
[exists_lexmax_nw_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean)
-/
@[path]
private lemma exists_lexmax_nw_corner_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  ∃ i : Fin n, d i = 1 ∧ d (i + 1) = 2 := by
-- proof
  apply StatMech.Onsager.InsideClimb.exists_lexmax_nw_corner d hclosed hreflexfree

/--
[cc_eq_four_of_selfAvoidanceWall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean)
-/
@[path]
private lemma cc_eq_four_of_selfAvoidanceWall_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (hwall : two_nw_corners_not_injective d) :
-- imply
  cc d = 4 := by
-- proof
  apply StatMech.Onsager.InsideClimb.cc_eq_four_of_selfAvoidanceWall d hclosed hsimple hreflexfree hwall


-- created on 2026-10-23
