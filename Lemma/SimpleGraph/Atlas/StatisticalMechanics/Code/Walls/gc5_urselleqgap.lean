import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc5_urselleqgap
open Finset SimpleGraph Set StatMech StatMech.Walls StatMech.Walls.Gc5EqGap


/--
[gc5_ursellEqGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_urselleqgap.lean)
-/
@[path]
private lemma gc5_ursellEqGap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y = eg_ursell4_ghost G β h o x y + 2 * eg_tripleProduct G β h o x y := by
-- proof
  apply StatMech.Walls.Gc5EqGap.gc5_ursellEqGap G β h o x y

/--
[gc5_ursell4_ghost_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_urselleqgap.lean)
-/
@[path]
private lemma gc5_ursell4_ghost_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell4_ghost G β h o x y = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y)) - isingExpectation G β h (fun s => spin s o * spin s x) * isingExpectation G β h (fun s => spin s y) - isingExpectation G β h (fun s => spin s o * spin s y) * isingExpectation G β h (fun s => spin s x) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x * spin s y) := by
-- proof
  apply StatMech.Walls.Gc5EqGap.gc5_ursell4_ghost_eq G β h o x y

/--
[gc5_ursell3_eq_ursell4_ghost_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_urselleqgap.lean)
-/
@[path]
private lemma gc5_ursell3_eq_ursell4_ghost_sub_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell4_ghost G β h o x y = eg_ursell3 G β h o x y - 2 * eg_tripleProduct G β h o x y := by
-- proof
  apply StatMech.Walls.Gc5EqGap.gc5_ursell3_eq_ursell4_ghost_sub G β h o x y

/--
[gc5_ursell4_ghost_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_urselleqgap.lean)
-/
@[path]
private lemma gc5_ursell4_ghost_swap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell4_ghost G β h o x y = eg_ursell4_ghost G β h o y x := by
-- proof
  apply StatMech.Walls.Gc5EqGap.gc5_ursell4_ghost_swap G β h o x y

/--
[gc5_ursell4_ghost_eq_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_urselleqgap.lean)
-/
@[path]
private lemma gc5_ursell4_ghost_eq_gap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell4_ghost G β h o x y = (cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y)) - 2 * eg_tripleProduct G β h o x y := by
-- proof
  apply StatMech.Walls.Gc5EqGap.gc5_ursell4_ghost_eq_gap G β h o x y

/--
[gc5_ghs_iff_ursell4_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_urselleqgap.lean)
-/
@[path]
private lemma gc5_ghs_iff_ursell4_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) ↔ eg_ursell4_ghost G β h o x y ≤ -2 * eg_tripleProduct G β h o x y := by
-- proof
  apply StatMech.Walls.Gc5EqGap.gc5_ghs_iff_ursell4_ghost G β h o x y

/--
[gc5_ursell4_ghost_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_urselleqgap.lean)
-/
@[path]
private lemma gc5_ursell4_ghost_degenerate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell4_ghost G β h x x y = -2 * isingExpectation G β h (fun s => spin s x) * cov2 G β h x y - 2 * (isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s x)) * isingExpectation G β h (fun s => spin s y) := by
-- proof
  apply StatMech.Walls.Gc5EqGap.gc5_ursell4_ghost_degenerate G β h x y

/--
[gc5_ursell4_ghost_nonpos_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_urselleqgap.lean)
-/
@[path]
private lemma gc5_ursell4_ghost_nonpos_degenerate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hxy : x ≠ y) :
-- imply
  eg_ursell4_ghost G β h x x y ≤ 0 := by
-- proof
  apply StatMech.Walls.Gc5EqGap.gc5_ursell4_ghost_nonpos_degenerate G β h hβ hh x y hxy

/--
[gc5_ghs_of_ursell4_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_urselleqgap.lean)
-/
@[path]
private lemma gc5_ghs_of_ursell4_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (h0 : ∀ x y : V, eg_ursell4_ghost G β h o x y ≤ -2 * eg_tripleProduct G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.Gc5EqGap.gc5_ghs_of_ursell4_ghost G β h o h0


-- created on 2026-10-23
