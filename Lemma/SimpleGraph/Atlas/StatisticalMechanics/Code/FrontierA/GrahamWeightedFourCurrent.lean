import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourCurrent
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[fourSources_symmDiff_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourCurrent.lean)
-/
@[path]
private lemma fourSources_symmDiff_pair_eq
  [Fintype V]
  [DecidableEq V]
  {i j k l : V}
-- given
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  ({i, j, k, l} : Finset V) ∆ {i, j} = {k, l} := by
-- proof
  apply StatMech.FrontierA.fourSources_symmDiff_pair hij hik hil hjk hjl hkl

/--
[gatedSourcePairSum_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourCurrent.lean)
-/
@[path]
private lemma gatedSourcePairSum_true_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  gatedSourcePairSum G beta J A B (fun _ => True) = sourcePairSum G beta J A B := by
-- proof
  apply StatMech.FrontierA.gatedSourcePairSum_true G beta J A B

/--
[grahamPairProduct_eq_connectedMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourCurrent.lean)
-/
@[path]
private lemma grahamPairProduct_eq_connectedMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  currentSum G beta J {i, j} * currentSum G beta J {k, l} = gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun m => CurrentConnected G m i j) := by
-- proof
  apply StatMech.FrontierA.grahamPairProduct_eq_connectedMass G beta J hij hik hil hjk hjl hkl

/--
[grahamCurrent_one_or_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourCurrent.lean)
-/
@[path]
private lemma grahamCurrent_one_or_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (m : ↥G.edgeFinset -> Nat)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l)
  (hsrc : sources G (ofEdgeFun G m) = {i, j, k, l}) :
-- imply
  #(({j, k, l} : Finset V).filter (fun x => CurrentConnected G (ofEdgeFun G m) i x)) = 1 ∨ #(({j, k, l} : Finset V).filter (fun x => CurrentConnected G (ofEdgeFun G m) i x)) = 3 := by
-- proof
  apply StatMech.FrontierA.grahamCurrent_one_or_three G m hij hik hil hjk hjl hkl hsrc

/--
[grahamFourSource_indicator_cancellation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourCurrent.lean)
-/
@[path]
private lemma grahamFourSource_indicator_cancellation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (m : ↥G.edgeFinset -> Nat)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l)
  (hsrc : sources G (ofEdgeFun G m) = {i, j, k, l}) :
-- imply
  (1 : Real) - (if CurrentConnected G (ofEdgeFun G m) i j then 1 else 0) - (if CurrentConnected G (ofEdgeFun G m) i k then 1 else 0) - (if CurrentConnected G (ofEdgeFun G m) i l then 1 else 0) = -2 * (if grahamAllThreeConnected G (ofEdgeFun G m) i j k l then 1 else 0) := by
-- proof
  apply StatMech.FrontierA.grahamFourSource_indicator_cancellation G m hij hik hil hjk hjl hkl hsrc

/--
[grahamWeightedFourSource_cancellation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourCurrent.lean)
-/
@[path]
private lemma grahamWeightedFourSource_cancellation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun _ => True) - gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun m => CurrentConnected G m i j) - gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun m => CurrentConnected G m i k) - gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun m => CurrentConnected G m i l) = -2 * gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun m => grahamAllThreeConnected G m i j k l) := by
-- proof
  apply StatMech.FrontierA.grahamWeightedFourSource_cancellation G beta J hij hik hil hjk hjl hkl

/--
[grahamCurrentSum_ursell4_eq_allThree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourCurrent.lean)
-/
@[path]
private lemma grahamCurrentSum_ursell4_eq_allThree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  currentSum G beta J {i, j, k, l} * currentSum G beta J ∅ - currentSum G beta J {i, j} * currentSum G beta J {k, l} - currentSum G beta J {i, k} * currentSum G beta J {j, l} - currentSum G beta J {i, l} * currentSum G beta J {j, k} = -2 * gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun m => grahamAllThreeConnected G m i j k l) := by
-- proof
  apply StatMech.FrontierA.grahamCurrentSum_ursell4_eq_allThree G beta J hij hik hil hjk hjl hkl


-- created on 2026-10-23
