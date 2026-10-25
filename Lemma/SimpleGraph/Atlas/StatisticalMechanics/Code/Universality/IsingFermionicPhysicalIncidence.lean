import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalIncidence
open StatMech StatMech.Universality


/--
[fkIsingSquareWired_incidence_infix_explorationOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalIncidence.lean)
-/
@[path]
private lemma fkIsingSquareWired_incidence_infix_explorationOrder_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : (.dart d : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
-- imply
  [(.dart d : FKIsingSquareWiredCarrier n), .bond d] <:+: fkIsingSquareWiredExplorationOrder n hn omega ∨ [(.bond d : FKIsingSquareWiredCarrier n), .dart d] <:+: fkIsingSquareWiredExplorationOrder n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_incidence_infix_explorationOrder n hn omega d h

/--
[fkIsingSquareWiredRawTurnCount_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalIncidence.lean)
-/
@[path]
private lemma fkIsingSquareWiredRawTurnCount_incidence_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : (.dart d : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn omega (.bond d) = fkIsingSquareWiredRawTurnCount n hn omega (.dart d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRawTurnCount_incidence n hn omega d h

/--
[fkIsingSquareWiredLiftedWinding_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalIncidence.lean)
-/
@[path]
private lemma fkIsingSquareWiredLiftedWinding_incidence_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : (.dart d : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn omega (.bond d) = fkIsingSquareWiredLiftedWinding n hn omega (.dart d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLiftedWinding_incidence n hn omega d h

/--
[fkIsingSquareWired_incidence_mem_trace_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalIncidence.lean)
-/
@[path]
private lemma fkIsingSquareWired_incidence_mem_trace_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (.bond d : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn omega ↔ (.dart d : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_incidence_mem_trace_iff n hn omega d

/--
[fkIsingSquareWired_fermionicSummand_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalIncidence.lean)
-/
@[path]
private lemma fkIsingSquareWired_fermionicSummand_incidence_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega (.bond d) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega (.dart d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_fermionicSummand_incidence n hn omega d

/--
[fkIsingSquareWired_fermionicObservable_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalIncidence.lean)
-/
@[path]
private lemma fkIsingSquareWired_fermionicObservable_incidence_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.bond d) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_fermionicObservable_incidence n hn d

/--
[fkIsingSquareWiredPrimitiveIncrement_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalIncidence.lean)
-/
@[path]
private lemma fkIsingSquareWiredPrimitiveIncrement_incidence_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn (.bond d) = fkIsingSquareWiredPrimitiveIncrement n hn (.dart d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPrimitiveIncrement_incidence n hn d


-- created on 2026-10-23
