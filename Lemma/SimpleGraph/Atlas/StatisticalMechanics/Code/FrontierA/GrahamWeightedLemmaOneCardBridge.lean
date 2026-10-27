import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneCardBridge.Part2
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamFourSplitMultiplicity_eq_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneCardBridge.lean)
-/
@[path]
private lemma grahamFourSplitMultiplicity_eq_natCast_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : GrahamFourSplit G total}
-- given
  (total : G.edgeFinset -> Nat) :
-- imply
  grahamFourSplitMultiplicity G total s = (grahamFourSplitMultiplicityNat G total s : Real) := by
-- proof
  apply StatMech.FrontierA.grahamFourSplitMultiplicity_eq_natCast G total s

/--
[grahamMixedProfileIndicator_eq_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneCardBridge.lean)
-/
@[path]
private lemma grahamMixedProfileIndicator_eq_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {j k l m : V}
  {q : GrahamFourColoring (Copy G total)}
-- given
  (total : G.edgeFinset -> Nat)
  (hq : q.IsPartition Finset.univ) :
-- imply
  grahamMixedProfileIndicator G total (profileFlux G total q.color1) (profileFlux G total q.color2) (profileFlux G total q.color3) j k l m = if q ∈ grahamLemmaOneMixedColorings (endsM G total) Finset.univ j k l m then 1 else 0 := by
-- proof
  apply StatMech.FrontierA.grahamMixedProfileIndicator_eq_mem G total j k l m q hq

/--
[grahamLemmaOneMixedProfileCoefficient_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneCardBridge.lean)
-/
@[path]
private lemma grahamLemmaOneMixedProfileCoefficient_eq_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {j k l m : V}
-- given
  (total : G.edgeFinset -> Nat) :
-- imply
  grahamLemmaOneMixedProfileCoefficient G total j k l m = (#(grahamLemmaOneMixedColorings (endsM G total) Finset.univ j k l m) : Real) := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneMixedProfileCoefficient_eq_card G total j k l m

/--
[grahamSeparatedProfileIndicator_eq_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneCardBridge.lean)
-/
@[path]
private lemma grahamSeparatedProfileIndicator_eq_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {j k l m : V}
  {q : GrahamFourColoring (Copy G total)}
-- given
  (total : G.edgeFinset -> Nat)
  (hq : q.IsPartition Finset.univ) :
-- imply
  grahamSeparatedProfileIndicator G total (profileFlux G total q.color1) (profileFlux G total q.color2) (profileFlux G total q.color3) j k l m = if q ∈ grahamLemmaOneSeparatedColorings (endsM G total) Finset.univ j k l m then 1 else 0 := by
-- proof
  apply StatMech.FrontierA.grahamSeparatedProfileIndicator_eq_mem G total j k l m q hq

/--
[grahamLemmaOneSeparatedProfileCoefficient_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneCardBridge.lean)
-/
@[path]
private lemma grahamLemmaOneSeparatedProfileCoefficient_eq_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {j k l m : V}
-- given
  (total : G.edgeFinset -> Nat) :
-- imply
  grahamLemmaOneSeparatedProfileCoefficient G total j k l m = (#(grahamLemmaOneSeparatedColorings (endsM G total) Finset.univ j k l m) : Real) := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneSeparatedProfileCoefficient_eq_card G total j k l m


-- created on 2026-10-23
