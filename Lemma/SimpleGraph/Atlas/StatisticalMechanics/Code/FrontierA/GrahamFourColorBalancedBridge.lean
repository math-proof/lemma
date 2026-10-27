import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedBridge.Part2
open Finset Classical StatMech StatMech.FrontierA


/--
[mem_balanced_colorClass_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma mem_balanced_colorClass_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {a : Fin 4}
  {i : ι}
-- given
  (c : ↑U -> Fin 4) :
-- imply
  i ∈ colorClass U c a ↔ ∃ hi : i ∈ U, c ⟨i, hi⟩ = a := by
-- proof
  apply StatMech.FrontierA.mem_balanced_colorClass_iff U c a i

/--
[colorClass_grahamToBalancedColor_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma colorClass_grahamToBalancedColor_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {q : GrahamFourColoring ι}
-- given
  (hq : q.IsPartition U) :
-- imply
  colorClass U (grahamToBalancedColor U q) 0 = q.color1 := by
-- proof
  apply StatMech.FrontierA.colorClass_grahamToBalancedColor_zero U q hq

/--
[colorClass_grahamToBalancedColor_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma colorClass_grahamToBalancedColor_one_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {q : GrahamFourColoring ι}
-- given
  (hq : q.IsPartition U) :
-- imply
  colorClass U (grahamToBalancedColor U q) 1 = q.color2 := by
-- proof
  apply StatMech.FrontierA.colorClass_grahamToBalancedColor_one U q hq

/--
[colorClass_grahamToBalancedColor_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma colorClass_grahamToBalancedColor_two_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {q : GrahamFourColoring ι}
-- given
  (hq : q.IsPartition U) :
-- imply
  colorClass U (grahamToBalancedColor U q) 2 = q.color3 := by
-- proof
  apply StatMech.FrontierA.colorClass_grahamToBalancedColor_two U q hq

/--
[colorClass_grahamToBalancedColor_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma colorClass_grahamToBalancedColor_three_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {q : GrahamFourColoring ι}
-- given
  (hq : q.IsPartition U) :
-- imply
  colorClass U (grahamToBalancedColor U q) 3 = q.color4 U := by
-- proof
  apply StatMech.FrontierA.colorClass_grahamToBalancedColor_three U q hq

/--
[grahamToBalancedColor_leftPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma grahamToBalancedColor_leftPattern_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {j k l m : W}
  {q : GrahamFourColoring ι}
-- given
  (ends : ι -> Sym2 W)
  (hq : q ∈ grahamLemmaOneSeparatedColorings ends U j k l m) :
-- imply
  LeftPattern ends U {j, k} {k, l} k m (grahamToBalancedColor U q) := by
-- proof
  apply StatMech.FrontierA.grahamToBalancedColor_leftPattern ends U j k l m q hq

/--
[balancedColorToGraham_color4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma balancedColorToGraham_color4_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
-- given
  (c : ↑U -> Fin 4) :
-- imply
  (balancedColorToGraham U c).color4 U = colorClass U c 3 := by
-- proof
  apply StatMech.FrontierA.balancedColorToGraham_color4 U c

/--
[balancedColorToGraham_isPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma balancedColorToGraham_isPartition_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
-- given
  (c : ↑U -> Fin 4) :
-- imply
  (balancedColorToGraham U c).IsPartition U := by
-- proof
  apply StatMech.FrontierA.balancedColorToGraham_isPartition U c

/--
[balancedColorToGraham_grahamToBalancedColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma balancedColorToGraham_grahamToBalancedColor_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {q : GrahamFourColoring ι}
-- given
  (hq : q.IsPartition U) :
-- imply
  balancedColorToGraham U (grahamToBalancedColor U q) = q := by
-- proof
  apply StatMech.FrontierA.balancedColorToGraham_grahamToBalancedColor U q hq

/--
[grahamToBalancedColor_balancedColorToGraham](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma grahamToBalancedColor_balancedColorToGraham_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
-- given
  (c : ↑U -> Fin 4) :
-- imply
  grahamToBalancedColor U (balancedColorToGraham U c) = c := by
-- proof
  apply StatMech.FrontierA.grahamToBalancedColor_balancedColorToGraham U c

/--
[balancedColorToGraham_mixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma balancedColorToGraham_mixed_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {j k l m : W}
-- given
  (ends : ι -> Sym2 W)
  (c : ↑U -> Fin 4)
  (hc : RightPattern ends U {j, k} {k, l} k m c) :
-- imply
  balancedColorToGraham U c ∈ grahamLemmaOneMixedColorings ends U j k l m := by
-- proof
  apply StatMech.FrontierA.balancedColorToGraham_mixed ends U j k l m c hc

/--
[grahamLemmaOne_card_le_of_balancedMinor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma grahamLemmaOne_card_le_of_balancedMinor_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {j k l m : W}
-- given
  (ends : ι -> Sym2 W)
  (hminor : GrahamFiberMinor ends U j k l m) :
-- imply
  #(grahamLemmaOneSeparatedColorings ends U j k l m) ≤ #(grahamLemmaOneMixedColorings ends U j k l m) := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOne_card_le_of_balancedMinor ends U j k l m hminor

/--
[grahamLemmaOne_card_le_of_total_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean)
-/
@[path]
private lemma grahamLemmaOne_card_le_of_total_disconnected_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {j k l m : W}
-- given
  (ends : ι -> Sym2 W)
  (hdisc : ¬connK ends U k m) :
-- imply
  #(grahamLemmaOneSeparatedColorings ends U j k l m) ≤ #(grahamLemmaOneMixedColorings ends U j k l m) := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOne_card_le_of_total_disconnected ends U j k l m hdisc


-- created on 2026-10-23
