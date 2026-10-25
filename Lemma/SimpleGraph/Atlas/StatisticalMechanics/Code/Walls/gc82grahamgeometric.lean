import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc82grahamgeometric.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc82_ThreeGapNonpos_iff_gc15](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_ThreeGapNonpos_iff_gc15_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  gc82_ThreeGapNonpos G β h o x y ↔ gc15_PerConfigUrsellSign G β h o x y := by
-- proof
  apply StatMech.Walls.gc82_ThreeGapNonpos_iff_gc15 G β h o x y

/--
[gc82_gated_eq_ungated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_gated_eq_ungated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  (if gc82_allConn G β h o x y m then (- (1/2) * gc15_threeGap G β h o x y m) else 0) = - (1/2) * gc15_threeGap G β h o x y m := by
-- proof
  apply StatMech.Walls.gc82_gated_eq_ungated G β h o x y hsupp m

/--
[gc82_delta3_eq_neg_half_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_delta3_eq_neg_half_tsum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  gc82_delta3 G β h o x y = - (1/2) * ∑' m, gc15_threeGap G β h o x y m := by
-- proof
  apply StatMech.Walls.gc82_delta3_eq_neg_half_tsum G β h o x y hsupp

/--
[gc82_summand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_summand_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hsign : gc82_ThreeGapNonpos G β h o x y) :
-- imply
  0 ≤ (if gc82_allConn G β h o x y m then (- (1/2) * gc15_threeGap G β h o x y m) else 0) := by
-- proof
  apply StatMech.Walls.gc82_summand_nonneg G β h o x y hsign m

/--
[gc82_delta3_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_delta3_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hsign : gc82_ThreeGapNonpos G β h o x y) :
-- imply
  0 ≤ gc82_delta3 G β h o x y := by
-- proof
  apply StatMech.Walls.gc82_delta3_nonneg G β h o x y hsign

/--
[gc82_grahamResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_grahamResummation_eq
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
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = -2 * gc82_delta3 G β h o x y := by
-- proof
  apply StatMech.Walls.gc82_grahamResummation G β h o x y hox hoy hxy hsupp

/--
[gc82_delta3_eq_gc81](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_delta3_eq_gc81_eq
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
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  gc82_delta3 G β h o x y = gc81_grahamAllConnMass G β h o x y := by
-- proof
  apply StatMech.Walls.gc82_delta3_eq_gc81 G β h o x y hox hoy hxy hsupp

/--
[gc82_ursell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_ursell_nonpos_eq
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
  (hsign : gc82_ThreeGapNonpos G β h o x y)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc82_ursell_nonpos G β h o x y hox hoy hxy hsign hsupp

/--
[gc82_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc82_ThreeGapNonpos G β h o x y)
  (hsupp : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc82_ghs G β h hβ hh o hsign hsupp

/--
[gc82_aizenman_barsky](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_aizenman_barsky_eq
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
  (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc82_ThreeGapNonpos G β h o x y)
  (hsupp : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc82_ThreeGapAllConnSupported G β h o x y)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc82_aizenman_barsky G β h hβ hh o J hsign hsupp hfactor

/--
[gc82_delta3_at_zero_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_delta3_at_zero_of_residues_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hsupp : gc82_ThreeGapAllConnSupported G β 0 o x y) :
-- imply
  gc82_delta3 G β 0 o x y = 0 := by
-- proof
  apply StatMech.Walls.gc82_delta3_at_zero_of_residues G β o x y hox hoy hxy hsupp

/--
[gc82_delta3_eq_gc81_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_delta3_eq_gc81_at_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hsupp : gc82_ThreeGapAllConnSupported G β 0 o x y) :
-- imply
  gc82_delta3 G β 0 o x y = gc81_grahamAllConnMass G β 0 o x y := by
-- proof
  apply StatMech.Walls.gc82_delta3_eq_gc81_at_zero G β o x y hox hoy hxy hsupp

/--
[gc82_graham_geometric_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean)
-/
@[path]
private lemma gc82_graham_geometric_status_eq
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
  (hsign : gc82_ThreeGapNonpos G β h o x y)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  ((gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = -2 * gc82_delta3 G β h o x y) ∧ (0 ≤ gc82_delta3 G β h o x y) ∧ (eg_ursell3 G β h o x y ≤ 0) := by
-- proof
  apply StatMech.Walls.gc82_graham_geometric_status G β h o x y hox hoy hxy hsign hsupp


-- created on 2026-10-23
