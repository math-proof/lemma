import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.ghxswitchingsign
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[ghx_eq24_U4_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_eq24_U4_nonpos_eq
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
  apply StatMech.Walls.ghx_eq24_U4_nonpos G β h hβ hh o x y hox hoy hxy

/--
[ghx_eq24_U4_nonpos_of_connRep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_eq24_U4_nonpos_of_connRep_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hrep : gc37_U4a_connRep G β h o x y) :
-- imply
  gc37_U4 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghx_eq24_U4_nonpos_of_connRep G β h hβ hh o x y hrep

/--
[ghx_ursell3_eq_U4_add_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_ursell3_eq_U4_add_triple_eq
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
  apply StatMech.Walls.ghx_ursell3_eq_U4_add_triple G β h o x y

/--
[ghx_triple_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_triple_nonneg_eq
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
  apply StatMech.Walls.ghx_triple_nonneg G β h hβ hh o x y

/--
[ghx_standardGHS_iff_sharpResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_standardGHS_iff_sharpResidue_eq
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
  apply StatMech.Walls.ghx_standardGHS_iff_sharpResidue G β h o x y

/--
[ghx_eq24_gives_only_ursell_le_two_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_eq24_gives_only_ursell_le_two_triple_eq
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
  apply StatMech.Walls.ghx_eq24_gives_only_ursell_le_two_triple G β h hβ hh o x y hox hoy hxy

/--
[ghx_eq24_wrong_sign_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_eq24_wrong_sign_obstruction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ a b : ℝ, a ≤ 0 ∧ 0 ≤ b ∧ 0 < a + 2 * b := by
-- proof
  apply StatMech.Walls.ghx_eq24_wrong_sign_obstruction G

/--
[ghx_standardGHS_of_perConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_standardGHS_of_perConfig_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.ghx_standardGHS_of_perConfig G β h hβ hh o hsign

/--
[ghx_standardGHS_of_fiberRegime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_standardGHS_of_fiberRegime_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hreg : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc20_FiberConnRegime G β h o x y m) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.ghx_standardGHS_of_fiberRegime G β h hβ hh o hreg

/--
[ghx_perConfig_implies_sharpResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_perConfig_implies_sharpResidue_eq
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
  (hsign : gc15_PerConfigUrsellSign G β h o x y) :
-- imply
  gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y := by
-- proof
  apply StatMech.Walls.ghx_perConfig_implies_sharpResidue G β h o x y hox hoy hxy hsign

/--
[ghx_standardGHS_of_sharpResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_standardGHS_of_sharpResidue_eq
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
  apply StatMech.Walls.ghx_standardGHS_of_sharpResidue G β h o x y hres

/--
[ghx_eq24_insufficient_for_standard_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_eq24_insufficient_for_standard_ghs_eq
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
  (gc37_U4 G β h o x y ≤ 0) ∧ (0 ≤ gc37_triple G β h o x y) ∧ (eg_ursell3 G β h o x y ≤ 0 ↔ gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y) ∧ (eg_ursell3 G β h o x y ≤ 2 * gc37_triple G β h o x y) ∧ (∀ hres : gc38_SharpGHSResidue G β h o x y, eg_ursell3 G β h o x y ≤ 0) := by
-- proof
  apply StatMech.Walls.ghx_eq24_insufficient_for_standard_ghs G β h hβ hh o x y hox hoy hxy

/--
[ghx_standardGHS_iff_residualStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_standardGHS_iff_residualStep_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 ↔ gc38_SharpGHSResidue G β h o x y := by
-- proof
  apply StatMech.Walls.ghx_standardGHS_iff_residualStep G β h o x y

/--
[ghx_sign_holds_at_h_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_sign_holds_at_h_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V} :
-- imply
  eg_ursell3 G β 0 o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghx_sign_holds_at_h_zero G β o x y

/--
[ghx_sign_holds_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_sign_holds_degenerate_eq
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
  eg_ursell3 G β h x x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghx_sign_holds_degenerate G β h hβ hh x y hxy

/--
[ghx_eq24_route_insufficient_offBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghxswitchingsign.lean)
-/
@[path]
private lemma ghx_eq24_route_insufficient_offBoundary_eq
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
  apply StatMech.Walls.ghx_eq24_route_insufficient_offBoundary G β h o x y hU4_le htriple_pos hU4_gt


-- created on 2026-10-23
