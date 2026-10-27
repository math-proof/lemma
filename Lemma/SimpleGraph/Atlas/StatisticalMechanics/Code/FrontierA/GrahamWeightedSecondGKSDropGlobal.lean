import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedSecondGKSDropGlobal
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamSecondRemainder_admissible_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDropGlobal.lean)
-/
@[path]
private lemma grahamSecondRemainder_admissible_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l m : V}
-- given
  (p q : G.edgeFinset -> Nat)
  (hkl : k ≠ l)
  (hp : sources G (ofEdgeFun G p) = {k, l})
  (hq : sources G (ofEdgeFun G q) = ∅) :
-- imply
  notConnComp G (ofEdgeFun G (fun e => p e + q e)) k ∈ grahamSecondAdmissibleComponentComplements i j k l m ↔ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) k m ∧ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) k i ∧ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) k j := by
-- proof
  apply StatMech.FrontierA.grahamSecondRemainder_admissible_iff G p q hkl hp hq

/--
[grahamSecondMixedRemainder_admissible_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDropGlobal.lean)
-/
@[path]
private lemma grahamSecondMixedRemainder_admissible_iff_eq
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
  (notConnComp G (ofEdgeFun G (fun e => p e + q e)) k ∈ grahamSecondAdmissibleComponentComplements i j k l m ∧ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i m) ↔ (¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i k ∧ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i m) := by
-- proof
  apply StatMech.FrontierA.grahamSecondMixedRemainder_admissible_iff G p q hij hkl hp hq

/--
[grahamSecondRemainderMass_eq_componentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDropGlobal.lean)
-/
@[path]
private lemma grahamSecondRemainderMass_eq_componentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hkl : k ≠ l) :
-- imply
  grahamSecondRemainderMass G beta J i j k l m = ∑ S ∈ grahamSecondAdmissibleComponentComplements i j k l m, grahamSecondComponentFiber G beta J S k {k, l} ∅ (fun _ => True) := by
-- proof
  apply StatMech.FrontierA.grahamSecondRemainderMass_eq_componentSum G beta J hkl

/--
[grahamSecondMixedRemainderMass_eq_componentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDropGlobal.lean)
-/
@[path]
private lemma grahamSecondMixedRemainderMass_eq_componentSum_eq
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
  grahamSecondMixedRemainderMass G beta J i j k l m = ∑ S ∈ grahamSecondAdmissibleComponentComplements i j k l m, grahamSecondComponentFiber G beta J S k {i, j} {k, l} (fun n => CurrentConnected G n i m) := by
-- proof
  apply StatMech.FrontierA.grahamSecondMixedRemainderMass_eq_componentSum G beta J hij hkl

/--
[grahamSecondGlobalGKSDrop_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDropGlobal.lean)
-/
@[path]
private lemma grahamSecondGlobalGKSDrop_nonneg_eq
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
  (hik : i ≠ k)
  (hil : i ≠ l)
  (him : i ≠ m)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  0 ≤ (currentSum G beta J {i, m} * currentSum G beta J {j, m}) * grahamSecondRemainderMass G beta J i j k l m - currentSum G beta J ∅ ^ 2 * grahamSecondMixedRemainderMass G beta J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamSecondGlobalGKSDrop_nonneg G beta J hbeta hJ hij hik hil him hjk hjl hjm hkl hkm hlm


-- created on 2026-10-23
