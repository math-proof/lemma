import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorDiagonal.Part3
open Finset Classical StatMech StatMech.FrontierA


/--
[grahamGlobalMiddleSwap_color1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean)
-/
@[path]
private lemma grahamGlobalMiddleSwap_color1_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : GrahamFourColoring ι} :
-- imply
  (grahamGlobalMiddleSwap q).color1 = q.color1 := by
-- proof
  apply StatMech.FrontierA.grahamGlobalMiddleSwap_color1 q

/--
[grahamGlobalMiddleSwap_color2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean)
-/
@[path]
private lemma grahamGlobalMiddleSwap_color2_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : GrahamFourColoring ι} :
-- imply
  (grahamGlobalMiddleSwap q).color2 = q.color3 := by
-- proof
  apply StatMech.FrontierA.grahamGlobalMiddleSwap_color2 q

/--
[grahamGlobalMiddleSwap_color3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean)
-/
@[path]
private lemma grahamGlobalMiddleSwap_color3_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : GrahamFourColoring ι} :
-- imply
  (grahamGlobalMiddleSwap q).color3 = q.color2 := by
-- proof
  apply StatMech.FrontierA.grahamGlobalMiddleSwap_color3 q

/--
[grahamGlobalMiddleSwap_color4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean)
-/
@[path]
private lemma grahamGlobalMiddleSwap_color4_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {q : GrahamFourColoring ι} :
-- imply
  (grahamGlobalMiddleSwap q).color4 U = q.color4 U := by
-- proof
  apply StatMech.FrontierA.grahamGlobalMiddleSwap_color4 U q

/--
[grahamGlobalMiddleSwap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean)
-/
@[path]
private lemma grahamGlobalMiddleSwap_involutive_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : GrahamFourColoring ι} :
-- imply
  grahamGlobalMiddleSwap (grahamGlobalMiddleSwap q) = q := by
-- proof
  apply StatMech.FrontierA.grahamGlobalMiddleSwap_involutive q

/--
[grahamGlobalMiddleSwap_isPartition_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean)
-/
@[path]
private lemma grahamGlobalMiddleSwap_isPartition_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {q : GrahamFourColoring ι} :
-- imply
  (grahamGlobalMiddleSwap q).IsPartition U ↔ q.IsPartition U := by
-- proof
  apply StatMech.FrontierA.grahamGlobalMiddleSwap_isPartition_iff U q

/--
[mem_finiteTreeDiagonalColorings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean)
-/
@[path]
private lemma mem_finiteTreeDiagonalColorings_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
  {q : GrahamFourColoring ι}
-- given
  (ends : ι -> Sym2 V) :
-- imply
  q ∈ finiteTreeDiagonalColorings ends U i j k l ↔ q.IsPartition U ∧ sources ends q.color1 = {i, j} ∧ sources ends q.color2 = ∅ ∧ sources ends q.color3 = {k, l} ∧ sources ends (q.color4 U) = ∅ ∧ connK ends (q.color1 ∪ q.color3) i k := by
-- proof
  apply StatMech.FrontierA.mem_finiteTreeDiagonalColorings ends U i j k l q

/--
[grahamGlobalMiddleSwap_mem_diagonal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean)
-/
@[path]
private lemma grahamGlobalMiddleSwap_mem_diagonal_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
  {q : GrahamFourColoring ι}
-- given
  (ends : ι -> Sym2 V) :
-- imply
  grahamGlobalMiddleSwap q ∈ finiteTreeDiagonalColorings ends U i j k l ↔ q ∈ finiteTreeMixedColorings ends U i j k l := by
-- proof
  apply StatMech.FrontierA.grahamGlobalMiddleSwap_mem_diagonal_iff ends U i j k l q

/--
[finiteTreeMixedColorings_card_eq_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean)
-/
@[path]
private lemma finiteTreeMixedColorings_card_eq_diagonal_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V) :
-- imply
  #(finiteTreeMixedColorings ends U i j k l) = #(finiteTreeDiagonalColorings ends U i j k l) := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedColorings_card_eq_diagonal ends U i j k l

/--
[finiteTreeMixedColorings_card_le_sum_of_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean)
-/
@[path]
private lemma finiteTreeMixedColorings_card_le_sum_of_diagonal_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (h : FiniteTreeDiagonalBranchInequality ends U i j k l) :
-- imply
  #(finiteTreeMixedColorings ends U i j k l) ≤ ∑ y : V, #(finiteTreeSeparatedBranchColorings ends U i j k l y) := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedColorings_card_le_sum_of_diagonal ends U i j k l h


-- created on 2026-10-23
