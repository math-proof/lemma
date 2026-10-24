import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc83crosspairing
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc83_threeGap_eq_fam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean)
-/
@[path]
private lemma gc83_threeGap_eq_fam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc15_threeGap G β h o x y m = (if gc83_fourMark G o x y m then gc83_fam1 G β h o x y m + 2 * gc83_fam2 G β h o x y m else 0) := by
-- proof
  apply StatMech.Walls.gc83_threeGap_eq_fam G β h o x y hox hoy hxy m

/--
[gc83_threeGap_zero_off_fourMark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean)
-/
@[path]
private lemma gc83_threeGap_zero_off_fourMark_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hm : ¬ gc83_fourMark G o x y m) :
-- imply
  gc15_threeGap G β h o x y m = 0 := by
-- proof
  apply StatMech.Walls.gc83_threeGap_zero_off_fourMark G β h o x y hox hoy hxy m hm

/--
[gc83_ghostCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean)
-/
@[path]
private lemma gc83_ghostCoupling_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ)
  (hh : 0 ≤ h) :
-- imply
  ∀ e : Sym2 (Option V), 0 ≤ ghostCoupling h β (fun _ => (1 : ℝ)) e := by
-- proof
  apply StatMech.Walls.gc83_ghostCoupling_nonneg G β h hh

/--
[gc83_weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean)
-/
@[path]
private lemma gc83_weight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Sharpness.Current (Option V)}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => (1 : ℝ))) n := by
-- proof
  apply StatMech.Walls.gc83_weight_nonneg G β h hβ hh n

/--
[gc83_fam2_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean)
-/
@[path]
private lemma gc83_fam2_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ gc83_fam2 G β h o x y m := by
-- proof
  apply StatMech.Walls.gc83_fam2_nonneg G β h hβ hh o x y m

/--
[gc83_netNonpos_iff_threeGapNonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean)
-/
@[path]
private lemma gc83_netNonpos_iff_threeGapNonpos_eq
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
  gc83_NetNonpos G β h o x y ↔ gc82_ThreeGapNonpos G β h o x y := by
-- proof
  apply StatMech.Walls.gc83_netNonpos_iff_threeGapNonpos G β h o x y hox hoy hxy

/--
[gc83_ursell_nonpos_of_netNonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean)
-/
@[path]
private lemma gc83_ursell_nonpos_of_netNonpos_eq
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
  (hnet : gc83_NetNonpos G β h o x y)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc83_ursell_nonpos_of_netNonpos G β h o x y hox hoy hxy hnet hsupp

/--
[gc83_ursell_nonpos_of_missingBijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean)
-/
@[path]
private lemma gc83_ursell_nonpos_of_missingBijection_eq
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
  (hbij : gc83_MissingBijection G β h o x y)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc83_ursell_nonpos_of_missingBijection G β h o x y hox hoy hxy hbij hsupp

/--
[gc83_crosspairing_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean)
-/
@[path]
private lemma gc83_crosspairing_status_eq
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
  (∀ m : ↥(withGhost G).edgeFinset → ℕ, gc15_threeGap G β h o x y m = (if gc83_fourMark G o x y m then gc83_fam1 G β h o x y m + 2 * gc83_fam2 G β h o x y m else 0)) ∧ (∀ m : ↥(withGhost G).edgeFinset → ℕ, 0 ≤ gc83_fam2 G β h o x y m) ∧ (gc83_NetNonpos G β h o x y ↔ gc82_ThreeGapNonpos G β h o x y) := by
-- proof
  apply StatMech.Walls.gc83_crosspairing_status G β h hβ hh o x y hox hoy hxy


-- created on 2026-10-23
