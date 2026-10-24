import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc95bdownstreamaudit
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc95b_ursell3_eq_U4_add_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc95bdownstreamaudit.lean)
-/
@[path]
private lemma gc95b_ursell3_eq_U4_add_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y = gc37_U4 G β h o x y + 2 * gc37_triple G β h o x y := by
-- proof
  apply StatMech.Walls.gc95b_ursell3_eq_U4_add_triple G β h o x y

/--
[gc95b_U4_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc95bdownstreamaudit.lean)
-/
@[path]
private lemma gc95b_U4_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc37_U4 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc95b_U4_nonpos G β h hβ hh o x y hox hoy hxy

/--
[gc95b_triple_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc95bdownstreamaudit.lean)
-/
@[path]
private lemma gc95b_triple_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ gc37_triple G β h o x y := by
-- proof
  apply StatMech.Walls.gc95b_triple_nonneg G β h hβ hh o x y

/--
[gc95b_U4_nonpos_gives_only_ursell_le_two_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc95bdownstreamaudit.lean)
-/
@[path]
private lemma gc95b_U4_nonpos_gives_only_ursell_le_two_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y ≤ 2 * gc37_triple G β h o x y := by
-- proof
  apply StatMech.Walls.gc95b_U4_nonpos_gives_only_ursell_le_two_triple G β h hβ hh o x y hox hoy hxy

/--
[gc95b_ghs_iff_U4_le_neg_two_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc95bdownstreamaudit.lean)
-/
@[path]
private lemma gc95b_ghs_iff_U4_le_neg_two_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 ↔ gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y := by
-- proof
  apply StatMech.Walls.gc95b_ghs_iff_U4_le_neg_two_triple G β h o x y

/--
[gc95b_ghs_of_sharp_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc95bdownstreamaudit.lean)
-/
@[path]
private lemma gc95b_ghs_of_sharp_residue_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hres : gc38_SharpGHSResidue G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc95b_ghs_of_sharp_residue G β h o x y hres

/--
[gc95b_U4_route_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc95bdownstreamaudit.lean)
-/
@[path]
private lemma gc95b_U4_route_insufficient_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hU4_le : gc37_U4 G β h o x y ≤ 0)
  (htriple_pos : 0 < gc37_triple G β h o x y)
  (hU4_gt : -2 * gc37_triple G β h o x y < gc37_U4 G β h o x y) :
-- imply
  ¬ (eg_ursell3 G β h o x y ≤ 0) := by
-- proof
  apply StatMech.Walls.gc95b_U4_route_insufficient G β h o x y hU4_le htriple_pos hU4_gt

/--
[gc95b_boundary_U4_suffices_only_at_triple_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc95bdownstreamaudit.lean)
-/
@[path]
private lemma gc95b_boundary_U4_suffices_only_at_triple_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (htriple_zero : gc37_triple G β h o x y = 0)
  (hU4_le : gc37_U4 G β h o x y ≤ 0) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc95b_boundary_U4_suffices_only_at_triple_zero G β h o x y htriple_zero hU4_le

/--
[gc95b_downstream_audit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc95bdownstreamaudit.lean)
-/
@[path]
private lemma gc95b_downstream_audit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (eg_ursell3 G β h o x y = gc37_U4 G β h o x y + 2 * gc37_triple G β h o x y) ∧ (0 ≤ gc37_triple G β h o x y) ∧ (gc37_U4 G β h o x y ≤ 0) ∧ (eg_ursell3 G β h o x y ≤ 0 ↔ gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y) ∧ (eg_ursell3 G β h o x y ≤ 2 * gc37_triple G β h o x y) := by
-- proof
  apply StatMech.Walls.gc95b_downstream_audit G β h hβ hh o x y hox hoy hxy


-- created on 2026-10-23
