import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamDisconnectedAuxiliaryClosure
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamLemmaOneSeparatedProfileCoefficient_le_of_total_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDisconnectedAuxiliaryClosure.lean)
-/
@[path]
private lemma grahamLemmaOneSeparatedProfileCoefficient_le_of_total_disconnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {j k l m : V}
-- given
  (total : G.edgeFinset -> Nat)
  (hdisc : ¬ CurrentConnected G (ofEdgeFun G total) k m) :
-- imply
  grahamLemmaOneSeparatedProfileCoefficient G total j k l m <= grahamLemmaOneMixedProfileCoefficient G total j k l m := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneSeparatedProfileCoefficient_le_of_total_disconnected G total j k l m hdisc

/--
[not_currentConnected_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDisconnectedAuxiliaryClosure.lean)
-/
@[path]
private lemma not_currentConnected_of_not_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {u v : V}
-- given
  (huv : ¬ G.Reachable u v) :
-- imply
  ¬ CurrentConnected G n u v := by
-- proof
  apply StatMech.FrontierA.not_currentConnected_of_not_reachable G n huv

/--
[grahamLemmaOneSeparatedProfileCoefficient_le_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDisconnectedAuxiliaryClosure.lean)
-/
@[path]
private lemma grahamLemmaOneSeparatedProfileCoefficient_le_of_not_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {j k l m : V}
-- given
  (total : G.edgeFinset -> Nat)
  (hkm : ¬ G.Reachable k m) :
-- imply
  grahamLemmaOneSeparatedProfileCoefficient G total j k l m <= grahamLemmaOneMixedProfileCoefficient G total j k l m := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneSeparatedProfileCoefficient_le_of_not_reachable G total j k l m hkm

/--
[sourcePairDisconnSum_eq_sourcePairSum_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDisconnectedAuxiliaryClosure.lean)
-/
@[path]
private lemma sourcePairDisconnSum_eq_sourcePairSum_of_not_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset V}
  {u v : V}
-- given
  (J : Sym2 V -> Real)
  (huv : ¬ G.Reachable u v) :
-- imply
  sourcePairDisconnSum G beta J A B u v = sourcePairSum G beta J A B := by
-- proof
  apply StatMech.FrontierA.sourcePairDisconnSum_eq_sourcePairSum_of_not_reachable G beta J A B huv

/--
[grahamWeightedLemmaOne_eq_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDisconnectedAuxiliaryClosure.lean)
-/
@[path]
private lemma grahamWeightedLemmaOne_eq_of_not_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hkm : ¬ G.Reachable k m) :
-- imply
  sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m = sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamWeightedLemmaOne_eq_of_not_reachable G beta J j k l m hkm

/--
[grahamWeightedLemmaOne_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDisconnectedAuxiliaryClosure.lean)
-/
@[path]
private lemma grahamWeightedLemmaOne_of_not_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hkm : ¬ G.Reachable k m) :
-- imply
  sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m <= sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamWeightedLemmaOne_of_not_reachable G beta J j k l m hkm


-- created on 2026-10-23
