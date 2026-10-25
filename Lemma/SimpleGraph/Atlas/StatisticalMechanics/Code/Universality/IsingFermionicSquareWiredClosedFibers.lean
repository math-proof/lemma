import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
open StatMech StatMech.Universality


/--
[fkIsingSquareWiredCompleted_closed_darts_reachable_of_not_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompleted_closed_darts_reachable_of_not_wired_eq
  {n : Nat}
  {d f : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hlabel : fkIsingSquareDartEndpoint n d = fkIsingSquareDartEndpoint n f)
  (hnot : ¬ fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d)) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable (.dart d) (.dart f) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompleted_closed_darts_reachable_of_not_wired n hn d f hlabel hnot

/--
[fkIsingSquareWiredCompleted_reachable_dart_same_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompleted_reachable_dart_same_label_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  ∃ d : FKIsingMedialDart (fkSquareBoxPlanar n), (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x (.dart d) ∧ fkIsingSquareWiredCarrierPrimalLabel n hn x = fkIsingSquareDartEndpoint n d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompleted_reachable_dart_same_label n hn omega x

/--
[fkIsingSquareWiredCompleted_closed_reachable_of_label_eq_not_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompleted_closed_reachable_of_label_eq_not_wired_eq
  {n : Nat}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hlabel : fkIsingSquareWiredCarrierPrimalLabel n hn x = fkIsingSquareWiredCarrierPrimalLabel n hn y)
  (hnot : ¬ fkIsingSquareWiredArc n (fkIsingSquareWiredCarrierPrimalLabel n hn x)) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompleted_closed_reachable_of_label_eq_not_wired n hn x y hlabel hnot

/--
[fkIsingSquareWiredCompleted_closed_darts_reachable_of_same_wired_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompleted_closed_darts_reachable_of_same_wired_label_eq
  {n : Nat}
  {d f : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hlabel : fkIsingSquareDartEndpoint n d = fkIsingSquareDartEndpoint n f)
  (hwired : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d)) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable (.dart d) (.dart f) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompleted_closed_darts_reachable_of_same_wired_label n hn d f hlabel hwired

/--
[fkIsingSquareWiredCompleted_closed_reachable_of_wired_labels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompleted_closed_reachable_of_wired_labels_eq
  {n : Nat}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hx : fkIsingSquareWiredArc n (fkIsingSquareWiredCarrierPrimalLabel n hn x))
  (hy : fkIsingSquareWiredArc n (fkIsingSquareWiredCarrierPrimalLabel n hn y)) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompleted_closed_reachable_of_wired_labels n hn x y hx hy

/--
[fkIsingSquareWiredCompleted_closed_reachable_iff_primal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompleted_closed_reachable_iff_primal_eq
  {n : Nat}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable x y ↔ (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔ (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable (fkIsingSquareWiredCarrierPrimalLabel n hn x) (fkIsingSquareWiredCarrierPrimalLabel n hn y) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompleted_closed_reachable_iff_primal n hn x y

/--
[fkIsingSquareWired_empty_completed_componentCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean)
-/
@[path]
private lemma fkIsingSquareWired_empty_completed_componentCount_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).ConnectedComponent = (2 * n + 1) ^ 2 - 2 * n := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_empty_completed_componentCount n hn

/--
[fkIsingSquareWiredCompleted_closed_darts_reachable_of_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompleted_closed_darts_reachable_of_wired_eq
  {n : Nat}
  {d f : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hd : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d))
  (hf : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n f)) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable (.dart d) (.dart f) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompleted_closed_darts_reachable_of_wired n hn d f hd hf

/--
[fkIsingSquareWiredCompleted_closed_reachable_of_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompleted_closed_reachable_of_wired_eq
  {n : Nat}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hx : fkIsingSquareWiredArc n (fkIsingSquareWiredCarrierPrimalLabel n hn x))
  (hy : fkIsingSquareWiredArc n (fkIsingSquareWiredCarrierPrimalLabel n hn y)) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompleted_closed_reachable_of_wired n hn x y hx hy


-- created on 2026-10-23
