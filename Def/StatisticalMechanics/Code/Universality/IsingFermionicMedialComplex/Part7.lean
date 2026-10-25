/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part5
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

namespace FKIsingDobrushinMedialComplex

variable {P : PlanarZ2Subgraph} (C : FKIsingDobrushinMedialComplex P)


def localDarts (e : FKIsingMedialVertex P) : Fin 4 -> FKIsingMedialDart P
  | 0 => (e, .west)
  | 1 => (e, .east)
  | 2 => (e, .south)
  | 3 => (e, .north)


def toDobrushinDomain
    (hterminal : forall omega,
      (C.loopGraph omega).Reachable C.sourceDart C.terminalDart) :
    FKIsingDobrushinDomain P (FKIsingMedialDart P) where
  wiredArc := C.wiredArc
  markedA := C.markedA
  markedB := C.markedB
  markedA_mem := C.markedA_mem
  markedB_mem := C.markedB_mem
  sourceEdge := C.sourceDart
  terminalEdge := C.terminalDart
  medialPosition := C.medialPosition
  exploration := C.exploration
  source_mem := C.source_mem_exploration
  terminal_mem := fun omega => (C.mem_exploration_iff omega C.terminalDart).2
    (hterminal omega)
  winding := C.winding
  winding_terminal := C.winding_terminal


def caseTwoExplorationSwitchingLaw
    (hterminal : forall omega,
      (C.loopGraph omega).Reachable C.sourceDart C.terminalDart)
    (a b : P.V) (hab : P.G.Adj a b)
    (hclosedWest : forall omega,
      let e : FKIsingMedialVertex P :=
        ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
      (e, .west) ∈ C.exploration (setClosed e.1 omega))
    (hclosedEast : forall omega,
      let e : FKIsingMedialVertex P :=
        ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
      (e, .east) ∉ C.exploration (setClosed e.1 omega))
    (hseparated : forall omega,
      ¬(openSub P.G (setClosed s(a, b) omega) ⊔
        (C.toDobrushinDomain hterminal).wiring).Reachable a b)
    (hbalance : (C.toDobrushinDomain hterminal).ClosedOpenPairedBalance
      s(a, b) (localDarts
        ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩)) :
    (C.toDobrushinDomain hterminal).CaseTwoExplorationSwitchingLaw where
  crossingA := a
  crossingB := b
  crossing_adj := hab
  edges := localDarts
    ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
  closed_endpoints_not_reachable := hseparated
  closed_mem_zero := hclosedWest
  closed_not_mem_one := hclosedEast
  closed_mem_two := by
    intro omega
    let e : FKIsingMedialVertex P :=
      ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
    exact (C.closed_west_mem_iff_south omega e).1 (hclosedWest omega)
  closed_not_mem_three := by
    intro omega hnorth
    let e : FKIsingMedialVertex P :=
      ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
    exact hclosedEast omega
      ((C.closed_east_mem_iff_north omega e).2 hnorth)
  open_mem := by
    intro omega k
    let e : FKIsingMedialVertex P :=
      ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
    have hall := C.open_local_mem_of_closed_west_mem_not_east omega e
      (hclosedWest omega) (hclosedEast omega)
    fin_cases k
    · exact hall .west
    · exact hall .east
    · exact hall .south
    · exact hall .north
  paired_balance := hbalance


def caseOneExplorationSwitchingLaw
    (hterminal : forall omega,
      (C.loopGraph omega).Reachable C.sourceDart C.terminalDart)
    (a b : P.V) (hab : P.G.Adj a b)
    (hclosedWest : forall omega,
      let e : FKIsingMedialVertex P :=
        ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
      (e, .west) ∉ C.exploration (setClosed e.1 omega))
    (hclosedEast : forall omega,
      let e : FKIsingMedialVertex P :=
        ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
      (e, .east) ∉ C.exploration (setClosed e.1 omega))
    :
    (C.toDobrushinDomain hterminal).CaseOneExplorationSwitchingLaw where
  crossingA := a
  crossingB := b
  crossing_adj := hab
  edges := localDarts
    ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
  closed_not_mem := by
    intro omega k
    let e : FKIsingMedialVertex P :=
      ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
    fin_cases k
    · exact hclosedWest omega
    · exact hclosedEast omega
    · intro hsouth
      exact hclosedWest omega ((C.closed_west_mem_iff_south omega e).2 hsouth)
    · intro hnorth
      exact hclosedEast omega ((C.closed_east_mem_iff_north omega e).2 hnorth)
  open_not_mem := by
    intro omega k
    let e : FKIsingMedialVertex P :=
      ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
    have hall := C.open_local_not_mem_of_closed_west_east_not_mem omega e
      (hclosedWest omega) (hclosedEast omega)
    fin_cases k
    · exact hall .west
    · exact hall .east
    · exact hall .south
    · exact hall .north

end FKIsingDobrushinMedialComplex
end
end StatMech.Universality
