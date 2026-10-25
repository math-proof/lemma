import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamImprovementReduction
open StatMech StatMech.FrontierA


/--
[grahamCorrectionDemand_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean)
-/
@[path]
private lemma grahamCorrectionDemand_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l m : V} :
-- imply
  grahamCorrectionDemand E J i j k l m = 2 * (grahamBridgeGap E J i k m * grahamBridgeGap E J j k m * grahamTwoPoint E J k l) + 2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m * grahamBridgeGap E J i k m * grahamBridgeGap E J i l m) := by
-- proof
  apply StatMech.FrontierA.grahamCorrectionDemand_eq E J i j k l m

/--
[grahamCorrectionDemand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean)
-/
@[path]
private lemma grahamCorrectionDemand_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l m : V}
-- given
  (hJ : ∀ e ∈ E, 0 ≤ J e) :
-- imply
  0 ≤ grahamCorrectionDemand E J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamCorrectionDemand_nonneg E J hJ i j k l m

/--
[grahamCorrectedBound_iff_demand_le_surplus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean)
-/
@[path]
private lemma grahamCorrectedBound_iff_demand_le_surplus_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l m : V} :
-- imply
  grahamUrsell4 E J i j k l ≤ grahamCorrectedRHS E J i j k l m ↔ grahamCorrectionDemand E J i j k l m ≤ grahamLeadingSurplus E J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedBound_iff_demand_le_surplus E J i j k l m

/--
[grahamImprovement_eq_of_aux_eq_first_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean)
-/
@[path]
private lemma grahamImprovement_eq_of_aux_eq_first_third_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j l : V} :
-- imply
  grahamUrsell4 E J i j i l = grahamCorrectedRHS E J i j i l i := by
-- proof
  apply StatMech.FrontierA.grahamImprovement_eq_of_aux_eq_first_third E J i j l

/--
[grahamImprovement_eq_of_aux_eq_first_fourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean)
-/
@[path]
private lemma grahamImprovement_eq_of_aux_eq_first_fourth_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k : V} :
-- imply
  grahamUrsell4 E J i j k i = grahamCorrectedRHS E J i j k i i := by
-- proof
  apply StatMech.FrontierA.grahamImprovement_eq_of_aux_eq_first_fourth E J i j k

/--
[grahamImprovement_eq_of_aux_eq_first_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean)
-/
@[path]
private lemma grahamImprovement_eq_of_aux_eq_first_second_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i k l : V} :
-- imply
  grahamUrsell4 E J i i k l = grahamCorrectedRHS E J i i k l i := by
-- proof
  apply StatMech.FrontierA.grahamImprovement_eq_of_aux_eq_first_second E J i k l

/--
[grahamImprovement_eq_of_aux_eq_second_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean)
-/
@[path]
private lemma grahamImprovement_eq_of_aux_eq_second_third_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j l : V} :
-- imply
  grahamUrsell4 E J i j j l = grahamCorrectedRHS E J i j j l j := by
-- proof
  apply StatMech.FrontierA.grahamImprovement_eq_of_aux_eq_second_third E J i j l

/--
[grahamImprovement_eq_of_aux_eq_second_fourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean)
-/
@[path]
private lemma grahamImprovement_eq_of_aux_eq_second_fourth_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k : V} :
-- imply
  grahamUrsell4 E J i j k j = grahamCorrectedRHS E J i j k j j := by
-- proof
  apply StatMech.FrontierA.grahamImprovement_eq_of_aux_eq_second_fourth E J i j k

/--
[grahamImprovement_eq_of_aux_eq_third_fourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean)
-/
@[path]
private lemma grahamImprovement_eq_of_aux_eq_third_fourth_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k : V} :
-- imply
  grahamUrsell4 E J i j k k = grahamCorrectedRHS E J i j k k k := by
-- proof
  apply StatMech.FrontierA.grahamImprovement_eq_of_aux_eq_third_fourth E J i j k

/--
[grahamImprovement_eq_of_repeated_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean)
-/
@[path]
private lemma grahamImprovement_eq_of_repeated_aux_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l m : V}
-- given
  (h : (i = j ∧ m = i) ∨ (i = k ∧ m = i) ∨ (i = l ∧ m = i) ∨ (j = k ∧ m = j) ∨ (j = l ∧ m = j) ∨ (k = l ∧ m = k)) :
-- imply
  grahamUrsell4 E J i j k l = grahamCorrectedRHS E J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamImprovement_eq_of_repeated_aux E J i j k l m h


-- created on 2026-10-23
