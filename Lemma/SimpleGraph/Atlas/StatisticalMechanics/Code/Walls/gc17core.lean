import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc17core
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc17_tsum_threeGap_eq_u3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean)
-/
@[path]
private lemma gc17_tsum_threeGap_eq_u3_eq
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
  ∑' m, gc15_threeGap G β h o x y m = (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y := by
-- proof
  apply StatMech.Walls.gc17_tsum_threeGap_eq_u3 G β h o x y hox hoy hxy

/--
[gc17_tsum_threeGap_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean)
-/
@[path]
private lemma gc17_tsum_threeGap_summable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  Summable (gc15_threeGap G β h o x y) := by
-- proof
  apply StatMech.Walls.gc17_tsum_threeGap_summable G β h o x y

/--
[gc17_u3_eq_U4_plus_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean)
-/
@[path]
private lemma gc17_u3_eq_U4_plus_triple_eq
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
  eg_ursell3 G β h o x y = eg_ursell4_ghostPlus G β h o x y + 2 * (onePt G β h o * onePt G β h x * onePt G β h y) := by
-- proof
  apply StatMech.Walls.gc17_u3_eq_U4_plus_triple G β h o x y hox hoy hxy

/--
[gc17_triple_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean)
-/
@[path]
private lemma gc17_triple_nonneg_eq
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
  0 ≤ onePt G β h o * onePt G β h x * onePt G β h y := by
-- proof
  apply StatMech.Walls.gc17_triple_nonneg G β h hβ hh o x y

/--
[gc17_u3_le_triple_of_lebowitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean)
-/
@[path]
private lemma gc17_u3_le_triple_of_lebowitz_eq
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
  (hU4 : eg_ursell4_ghostPlus G β h o x y ≤ 0) :
-- imply
  eg_ursell3 G β h o x y ≤ 2 * (onePt G β h o * onePt G β h x * onePt G β h y) := by
-- proof
  apply StatMech.Walls.gc17_u3_le_triple_of_lebowitz G β h o x y hox hoy hxy hU4

/--
[gc17_ursell_nonpos_of_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean)
-/
@[path]
private lemma gc17_ursell_nonpos_of_dichotomy_eq
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
  (hdich : gc17_AggregateDichotomy G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc17_ursell_nonpos_of_dichotomy G β h o x y hox hoy hxy hdich

/--
[gc17_tsum_threeGap_nonpos_of_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean)
-/
@[path]
private lemma gc17_tsum_threeGap_nonpos_of_dichotomy_eq
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
  (hdich : gc17_AggregateDichotomy G β h o x y) :
-- imply
  ∑' m, gc15_threeGap G β h o x y m ≤ 0 := by
-- proof
  apply StatMech.Walls.gc17_tsum_threeGap_nonpos_of_dichotomy G β h o x y hox hoy hxy hdich

/--
[gc17_ghs_of_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean)
-/
@[path]
private lemma gc17_ghs_of_dichotomy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hdich : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc17_AggregateDichotomy G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc17_ghs_of_dichotomy G β h hβ hh o hdich

/--
[gc17_aizenman_barsky_of_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean)
-/
@[path]
private lemma gc17_aizenman_barsky_of_dichotomy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {Jsum : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hdich : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc17_AggregateDichotomy G β h o x y)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = Jsum * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ Jsum * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc17_aizenman_barsky_of_dichotomy G β h hβ hh o Jsum hdich hfactor

/--
[gc17_distinct_ursell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean)
-/
@[path]
private lemma gc17_distinct_ursell_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hdich : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc17_AggregateDichotomy G β h o x y)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc17_distinct_ursell_nonpos G β h o hdich hox hoy hxy


-- created on 2026-10-23
