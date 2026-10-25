import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
open SimpleGraph StatMech StatMech.Lattice


/--
[horizontalWallExtension_mem_support_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CollaredWalkCrossing.lean)
-/
@[path]
private lemma horizontalWallExtension_mem_support_iff_eq
  {alpha beta : Int}
  {x y z : Site 2}
  {W : (hypercubicLattice 2).Walk x y} :
-- imply
  z ∈ (horizontalWallExtension alpha beta W).support ↔ z ∈ (sw_horizSeg (x 1) alpha (x 0)).support ∨ z ∈ W.support ∨ z ∈ (sw_horizSeg (y 1) (y 0) beta).support := by
-- proof
  apply StatMech.Lattice.horizontalWallExtension_mem_support_iff alpha beta W

/--
[horizontalWallExtension_support_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CollaredWalkCrossing.lean)
-/
@[path]
private lemma horizontalWallExtension_support_rect_eq
  {alpha beta bottom top : Int}
  {x y : Site 2}
  {W : (hypercubicLattice 2).Walk x y}
-- given
  (hxBox : x ∈ rect alpha beta bottom top)
  (hyBox : y ∈ rect alpha beta bottom top)
  (hWBox : ∀ z ∈ W.support, z ∈ rect alpha beta bottom top) :
-- imply
  ∀ z ∈ (horizontalWallExtension alpha beta W).support, z ∈ rect alpha beta bottom top := by
-- proof
  apply StatMech.Lattice.horizontalWallExtension_support_rect W hxBox hyBox hWBox

/--
[collaredWalks_meet_on_original_supports](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CollaredWalkCrossing.lean)
-/
@[path]
private lemma collaredWalks_meet_on_original_supports_eq
  {alpha beta bottom top : Int}
  {x y a b : Site 2}
  {V : (hypercubicLattice 2).Walk x y}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hab : alpha < beta)
  (hbt : bottom ≤ top)
  (hxBox : x ∈ rect alpha beta bottom top)
  (hyBox : y ∈ rect alpha beta bottom top)
  (haBox : a ∈ rect alpha beta bottom top)
  (hbBox : b ∈ rect alpha beta bottom top)
  (hVBox : ∀ z ∈ V.support, z ∈ rect alpha beta bottom top)
  (hHBox : ∀ z ∈ H.support, z ∈ rect alpha beta bottom top)
  (hLower : ∀ z ∈ (horizontalWallExtension alpha beta H).support, z ∈ (sw_vertSeg (x 0) bottom (x 1)).support → z ∈ V.support)
  (hUpper : ∀ z ∈ (horizontalWallExtension alpha beta H).support, z ∈ (sw_vertSeg (y 0) (y 1) top).support → z ∈ V.support)
  (hLeft : ∀ z ∈ V.support, z ∈ (sw_horizSeg (a 1) alpha (a 0)).support → z ∈ H.support)
  (hRight : ∀ z ∈ V.support, z ∈ (sw_horizSeg (b 1) (b 0) beta).support → z ∈ H.support) :
-- imply
  ∃ z ∈ H.support, z ∈ V.support := by
-- proof
  apply StatMech.Lattice.collaredWalks_meet_on_original_supports hab hbt V H hxBox hyBox haBox hbBox hVBox hHBox hLower hUpper hLeft hRight


-- created on 2026-10-23
