import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc81grahamthreereplica.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc81_natRes_iff_residualZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_natRes_iff_residualZero_eq
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
  gc25_NativeResummation G β h o x y ↔ gc81_natRes_residual G β h o x y = 0 := by
-- proof
  apply StatMech.Walls.gc81_natRes_iff_residualZero G β h o x y hox hoy hxy

/--
[gc81_grahamResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_grahamResummation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = -2 * gc81_grahamAllConnMass G β h o x y := by
-- proof
  apply StatMech.Walls.gc81_grahamResummation G β h o x y

/--
[gc81_ursell_nonpos_iff_grahamMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_ursell_nonpos_iff_grahamMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 ↔ 0 ≤ gc81_grahamAllConnMass G β h o x y := by
-- proof
  apply StatMech.Walls.gc81_ursell_nonpos_iff_grahamMass_nonneg G β h o x y

/--
[gc81_grahamMass_sub_leadingGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_grahamMass_sub_leadingGap_eq
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
  gc81_grahamAllConnMass G β h o x y - gc25_nativeAllConnMass G β h o x y = - gc81_natRes_residual G β h o x y / 2 := by
-- proof
  apply StatMech.Walls.gc81_grahamMass_sub_leadingGap G β h o x y hox hoy hxy

/--
[gc81_grahamMass_eq_gap_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_grahamMass_eq_gap_iff_eq
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
  gc81_grahamAllConnMass G β h o x y = gc25_nativeAllConnMass G β h o x y ↔ gc25_NativeResummation G β h o x y := by
-- proof
  apply StatMech.Walls.gc81_grahamMass_eq_gap_iff G β h o x y hox hoy hxy

/--
[gc81_leadingGap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_leadingGap_nonneg_eq
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
  0 ≤ gc25_nativeAllConnMass G β h o x y := by
-- proof
  apply StatMech.Walls.gc81_leadingGap_nonneg G β h hβ hh o x y

/--
[gc81_absResidual_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_absResidual_nonzero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ z s4 ao ax ay pxy pox poy : ℝ, gc81_absResidual z s4 ao ax ay pxy pox poy ≠ 0 := by
-- proof
  apply StatMech.Walls.gc81_absResidual_nonzero G

/--
[gc81_natRes_residual_eq_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_natRes_residual_eq_abs_eq
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
  gc81_natRes_residual G β h o x y = gc81_absResidual (gc15_Z0 G β h) (cs81 G β h {some o, some x, some y, none}) (cs81 G β h {some o, none}) (cs81 G β h {some x, none}) (cs81 G β h {some y, none}) (cs81 G β h {some x, some y}) (cs81 G β h {some o, some x}) (cs81 G β h {some o, some y}) := by
-- proof
  apply StatMech.Walls.gc81_natRes_residual_eq_abs G β h o x y hox hoy hxy

/--
[gc81_ghs_of_grahamMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_ghs_of_grahamMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hmass : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → 0 ≤ gc81_grahamAllConnMass G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc81_ghs_of_grahamMass_nonneg G β h hβ hh o hmass

/--
[gc81_aizenman_barsky_of_grahamMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_aizenman_barsky_of_grahamMass_nonneg_eq
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
  (hmass : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → 0 ≤ gc81_grahamAllConnMass G β h o x y)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc81_aizenman_barsky_of_grahamMass_nonneg G β h hβ hh o J hmass hfactor

/--
[gc81_grahamMass_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_grahamMass_at_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V} :
-- imply
  gc81_grahamAllConnMass G β 0 o x y = 0 := by
-- proof
  apply StatMech.Walls.gc81_grahamMass_at_zero G β o x y

/--
[gc81_graham_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean)
-/
@[path]
private lemma gc81_graham_status_eq
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
  (gc25_NativeResummation G β h o x y ↔ gc81_natRes_residual G β h o x y = 0) ∧ ((gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = -2 * gc81_grahamAllConnMass G β h o x y) ∧ (eg_ursell3 G β h o x y ≤ 0 ↔ 0 ≤ gc81_grahamAllConnMass G β h o x y) := by
-- proof
  apply StatMech.Walls.gc81_graham_status G β h o x y hox hoy hxy


-- created on 2026-10-23
