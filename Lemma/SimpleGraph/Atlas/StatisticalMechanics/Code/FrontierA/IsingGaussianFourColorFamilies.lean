import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorFamilies
open Finset Classical StatMech StatMech.FrontierA


/--
[exists_finiteTree_sourceComponentSwitch_separatedBranchPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorFamilies.lean)
-/
@[path]
private lemma exists_finiteTree_sourceComponentSwitch_separatedBranchPattern_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hloop : ∀ e ∈ U, ¬(ends e).IsDiag)
  (hkl : k ≠ l)
  (hmix : FiniteTreeMixedPattern ends U i j k l c) :
-- imply
  ∃ y, FiniteTreeSeparatedBranchPattern ends U i j k l y (middleSwapOn U (finiteTreeSourceComponentTransfer ends U k c) c) := by
-- proof
  apply StatMech.FrontierA.exists_finiteTree_sourceComponentSwitch_separatedBranchPattern ends U c hloop hkl hmix

/--
[mem_finiteTreeMixedColorings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorFamilies.lean)
-/
@[path]
private lemma mem_finiteTreeMixedColorings_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
  {q : GrahamFourColoring ι}
-- given
  (ends : ι -> Sym2 V) :
-- imply
  q ∈ finiteTreeMixedColorings ends U i j k l ↔ q.IsPartition U ∧ sources ends q.color1 = {i, j} ∧ sources ends q.color2 = {k, l} ∧ sources ends q.color3 = ∅ ∧ sources ends (q.color4 U) = ∅ ∧ connK ends (q.color1 ∪ q.color2) i k := by
-- proof
  apply StatMech.FrontierA.mem_finiteTreeMixedColorings ends U i j k l q

/--
[mem_finiteTreeSeparatedBranchColorings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorFamilies.lean)
-/
@[path]
private lemma mem_finiteTreeSeparatedBranchColorings_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l y : V}
  {q : GrahamFourColoring ι}
-- given
  (ends : ι -> Sym2 V) :
-- imply
  q ∈ finiteTreeSeparatedBranchColorings ends U i j k l y ↔ q.IsPartition U ∧ sources ends q.color1 = {i, j} ∧ sources ends q.color2 = ∅ ∧ sources ends q.color3 = {k, l} ∧ sources ends (q.color4 U) = ∅ ∧ connK ends (q.color1 ∪ q.color2) i y ∧ connK ends (q.color3 ∪ q.color4 U) k y := by
-- proof
  apply StatMech.FrontierA.mem_finiteTreeSeparatedBranchColorings ends U i j k l y q

/--
[finiteTreeMixedPattern_grahamToBalancedColor_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorFamilies.lean)
-/
@[path]
private lemma finiteTreeMixedPattern_grahamToBalancedColor_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
  {q : GrahamFourColoring ι}
-- given
  (ends : ι -> Sym2 V)
  (hq : q.IsPartition U) :
-- imply
  FiniteTreeMixedPattern ends U i j k l (grahamToBalancedColor U q) ↔ sources ends q.color1 = {i, j} ∧ sources ends q.color2 = {k, l} ∧ sources ends q.color3 = ∅ ∧ sources ends (q.color4 U) = ∅ ∧ connK ends (q.color1 ∪ q.color2) i k := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedPattern_grahamToBalancedColor_iff ends U i j k l q hq

/--
[finiteTreeSeparatedBranchPattern_grahamToBalancedColor_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorFamilies.lean)
-/
@[path]
private lemma finiteTreeSeparatedBranchPattern_grahamToBalancedColor_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l y : V}
  {q : GrahamFourColoring ι}
-- given
  (ends : ι -> Sym2 V)
  (hq : q.IsPartition U) :
-- imply
  FiniteTreeSeparatedBranchPattern ends U i j k l y (grahamToBalancedColor U q) ↔ sources ends q.color1 = {i, j} ∧ sources ends q.color2 = ∅ ∧ sources ends q.color3 = {k, l} ∧ sources ends (q.color4 U) = ∅ ∧ connK ends (q.color1 ∪ q.color2) i y ∧ connK ends (q.color3 ∪ q.color4 U) k y := by
-- proof
  apply StatMech.FrontierA.finiteTreeSeparatedBranchPattern_grahamToBalancedColor_iff ends U i j k l y q hq

/--
[finiteTreeMixedColorings_card_le_sum_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorFamilies.lean)
-/
@[path]
private lemma finiteTreeMixedColorings_card_le_sum_of_injective_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (f : (↥(finiteTreeMixedColorings ends U i j k l)) -> Σ y : V, ↥(finiteTreeSeparatedBranchColorings ends U i j k l y))
  (hf : Function.Injective f) :
-- imply
  #(finiteTreeMixedColorings ends U i j k l) ≤ ∑ y : V, #(finiteTreeSeparatedBranchColorings ends U i j k l y) := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedColorings_card_le_sum_of_injective ends U i j k l f hf


-- created on 2026-10-23
