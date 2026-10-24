import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc27polyineq
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc27_tsumThreeGap_nonpos_iff_polyIneq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_tsumThreeGap_nonpos_iff_polyIneq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (∑' m, gc15_threeGap G β h o x y m) ≤ 0 ↔ gc27_GHSPolyIneq G β h o x y := by
-- proof
  apply StatMech.Walls.gc27_tsumThreeGap_nonpos_iff_polyIneq G β h o x y hox hoy hxy

/--
[gc27_ghs_iff_polyIneq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_ghs_iff_polyIneq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 ↔ gc27_GHSPolyIneq G β h o x y := by
-- proof
  apply StatMech.Walls.gc27_ghs_iff_polyIneq G β h o x y hox hoy hxy

/--
[gc27_polyIneq_closes_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_polyIneq_closes_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hpoly : gc27_GHSPolyIneq G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc27_polyIneq_closes_ghs G β h o x y hox hoy hxy hpoly

/--
[gc27_ghs_of_polyIneq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_ghs_of_polyIneq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hpoly : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc27_GHSPolyIneq G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc27_ghs_of_polyIneq G β h hβ hh o hpoly

/--
[gc27_aizenman_barsky_of_polyIneq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_aizenman_barsky_of_polyIneq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hpoly : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc27_GHSPolyIneq G β h o x y)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc27_aizenman_barsky_of_polyIneq G β h hβ hh o J hpoly hfactor

/--
[gc27_polyIneq_of_nativeResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_polyIneq_of_nativeResummation_eq
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
  (hxy : x ≠ y)
  (hres : gc25_NativeResummation G β h o x y) :
-- imply
  gc27_GHSPolyIneq G β h o x y := by
-- proof
  apply StatMech.Walls.gc27_polyIneq_of_nativeResummation G β h hβ hh o x y hox hoy hxy hres

/--
[gc27_threeUsedGaps_in_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_threeUsedGaps_in_family_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b c r q p t : ℝ}
-- given
  (hfam : gc27_TwoSourceGapFamily a b c r q p t) :
-- imply
  a * p ≤ t ∧ b * q ≤ t ∧ c * r ≤ t := by
-- proof
  apply StatMech.Walls.gc27_threeUsedGaps_in_family G a b c r q p t hfam

/--
[gc27_twoSourceGaps_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_twoSourceGaps_insufficient_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ a b c r q p t : ℝ, gc27_TwoSourceGapFamily a b c r q p t ∧ ¬ (t + 2 * (a * b * c) ≤ a * p + b * q + c * r) := by
-- proof
  apply StatMech.Walls.gc27_twoSourceGaps_insufficient G

/--
[gc27_tripleBound_not_from_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_tripleBound_not_from_family_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ a b c r q p t : ℝ, gc27_TwoSourceGapFamily a b c r q p t ∧ ¬ (2 * (a * b * c) ≤ a * p + b * q + c * r - t) := by
-- proof
  apply StatMech.Walls.gc27_tripleBound_not_from_family G

/--
[gc27_three_switchingGaps_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_three_switchingGaps_nonneg_eq
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
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) := by
-- proof
  apply StatMech.Walls.gc27_three_switchingGaps_nonneg G β h hβ hh o x y hox hoy hxy

/--
[gc27_obstruction_named](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean)
-/
@[path]
private lemma gc27_obstruction_named_eq
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
  (gc27_GHSPolyIneq G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0) ∧ (gc25_NativeResummation G β h o x y → gc27_GHSPolyIneq G β h o x y) ∧ (∃ a b c r q p t : ℝ, gc27_TwoSourceGapFamily a b c r q p t ∧ ¬ (t + 2 * (a * b * c) ≤ a * p + b * q + c * r)) := by
-- proof
  apply StatMech.Walls.gc27_obstruction_named G β h hβ hh o x y hox hoy hxy


-- created on 2026-10-23
