import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[mem_grahamFourColorings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneFourColor.lean)
-/
@[path]
private lemma mem_grahamFourColorings_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {c : GrahamFourColoring ι} :
-- imply
  c ∈ grahamFourColorings U ↔ c.IsPartition U := by
-- proof
  apply StatMech.FrontierA.mem_grahamFourColorings U c

/--
[mem_grahamLemmaOneMixedColorings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneFourColor.lean)
-/
@[path]
private lemma mem_grahamLemmaOneMixedColorings_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {j k l m : W}
  {c : GrahamFourColoring ι}
-- given
  (ends : ι -> Sym2 W) :
-- imply
  c ∈ grahamLemmaOneMixedColorings ends U j k l m ↔ c.IsPartition U ∧ sources ends c.color1 = {j, k} ∧ sources ends c.color2 = {k, l} ∧ sources ends c.color3 = ∅ ∧ sources ends (c.color4 U) = ∅ ∧ ¬ connK ends (c.color1 ∪ c.color2) k m := by
-- proof
  apply StatMech.FrontierA.mem_grahamLemmaOneMixedColorings ends U j k l m c

/--
[mem_grahamLemmaOneSeparatedColorings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneFourColor.lean)
-/
@[path]
private lemma mem_grahamLemmaOneSeparatedColorings_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {j k l m : W}
  {c : GrahamFourColoring ι}
-- given
  (ends : ι -> Sym2 W) :
-- imply
  c ∈ grahamLemmaOneSeparatedColorings ends U j k l m ↔ c.IsPartition U ∧ sources ends c.color1 = {j, k} ∧ sources ends c.color2 = ∅ ∧ sources ends c.color3 = {k, l} ∧ sources ends (c.color4 U) = ∅ ∧ ¬ connK ends (c.color1 ∪ c.color2) k m ∧ ¬ connK ends (c.color3 ∪ c.color4 U) k m := by
-- proof
  apply StatMech.FrontierA.mem_grahamLemmaOneSeparatedColorings ends U j k l m c


-- created on 2026-10-23
