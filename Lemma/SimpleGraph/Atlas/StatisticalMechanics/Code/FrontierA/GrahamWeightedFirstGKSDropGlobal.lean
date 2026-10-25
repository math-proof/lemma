import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFirstGKSDropGlobal.Part2
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamCurrentConnected_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDropGlobal.lean)
-/
@[path]
private lemma grahamCurrentConnected_add_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u v : V}
-- given
  (p q : G.edgeFinset -> Nat)
  (h : CurrentConnected G (ofEdgeFun G p) u v) :
-- imply
  CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) u v := by
-- proof
  apply StatMech.FrontierA.grahamCurrentConnected_add_right G p q h

/--
[grahamFirstRemainder_admissible_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDropGlobal.lean)
-/
@[path]
private lemma grahamFirstRemainder_admissible_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l m : V}
-- given
  (p q : G.edgeFinset -> Nat)
  (hij : i ≠ j)
  (hp : sources G (ofEdgeFun G p) = {i, j})
  (hq : sources G (ofEdgeFun G q) = ∅) :
-- imply
  notConnComp G (ofEdgeFun G (fun e => p e + q e)) i ∈ grahamFirstAdmissibleComponentComplements i j k l m ↔ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i m ∧ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i k ∧ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i l := by
-- proof
  apply StatMech.FrontierA.grahamFirstRemainder_admissible_iff G p q hij hp hq

/--
[grahamFirstMixedRemainder_admissible_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDropGlobal.lean)
-/
@[path]
private lemma grahamFirstMixedRemainder_admissible_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l m : V}
-- given
  (p q : G.edgeFinset -> Nat)
  (hij : i ≠ j)
  (hkl : k ≠ l)
  (hp : sources G (ofEdgeFun G p) = {i, j})
  (hq : sources G (ofEdgeFun G q) = {k, l}) :
-- imply
  notConnComp G (ofEdgeFun G (fun e => p e + q e)) i ∈ grahamFirstAdmissibleComponentComplements i j k l m ↔ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i m ∧ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i k := by
-- proof
  apply StatMech.FrontierA.grahamFirstMixedRemainder_admissible_iff G p q hij hkl hp hq

/--
[grahamFirstRemainderMass_eq_componentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDropGlobal.lean)
-/
@[path]
private lemma grahamFirstRemainderMass_eq_componentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j) :
-- imply
  grahamFirstRemainderMass G beta J i j k l m = ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l m, grahamFirstComponentFiber G beta J S i {i, j} ∅ := by
-- proof
  apply StatMech.FrontierA.grahamFirstRemainderMass_eq_componentSum G beta J hij

/--
[grahamFirstMixedRemainderMass_eq_componentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDropGlobal.lean)
-/
@[path]
private lemma grahamFirstMixedRemainderMass_eq_componentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  grahamFirstMixedRemainderMass G beta J i j k l m = ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l m, grahamFirstComponentFiber G beta J S i {i, j} {k, l} := by
-- proof
  apply StatMech.FrontierA.grahamFirstMixedRemainderMass_eq_componentSum G beta J hij hkl

/--
[grahamFirstGlobalGKSDrop_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDropGlobal.lean)
-/
@[path]
private lemma grahamFirstGlobalGKSDrop_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  0 ≤ currentSum G beta J {k, l} * grahamFirstRemainderMass G beta J i j k l m - currentSum G beta J ∅ * grahamFirstMixedRemainderMass G beta J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamFirstGlobalGKSDrop_nonneg G beta J hbeta hJ hij hkl


-- created on 2026-10-23
