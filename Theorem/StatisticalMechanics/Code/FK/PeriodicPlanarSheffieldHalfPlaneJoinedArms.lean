/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneInfiniteArm
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneStripUnion
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


@[simp] theorem walkOfChain_support (G : SimpleGraph V) (x : V)
    (l : List V) (h : List.IsChain G.Adj (x :: l)) :
    (walkOfChain G x l h).support = x :: l := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih =>
      have h' : G.Adj x y ∧ List.IsChain G.Adj (y :: l) := by
        simpa only [List.isChain_cons_cons] using h
      simp only [walkOfChain, SimpleGraph.Walk.support_cons]
      congr 1
      exact ih y _


theorem PeriodicGraph.connectedWithinSet_exists_openSubgraphWalk
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    {A : Set V} {x y : V}
    (h : omega ∈ P.connectedWithinSet A x y) :
    ∃ q : (P.openSubgraph omega).Walk x y,
      ∀ v ∈ q.support, v ∈ A := by
  rcases h with ⟨l, hchain, hlast, hregion⟩
  let q₀ := walkOfChain (P.openSubgraph omega) x l hchain
  let q : (P.openSubgraph omega).Walk x y := q₀.copy rfl hlast
  refine ⟨q, ?_⟩
  intro v hv
  apply hregion v
  have hv₀ : v ∈ q₀.support := by
    simpa only [q, SimpleGraph.Walk.support_copy] using hv
  rwa [walkOfChain_support] at hv₀


theorem PeriodicGraph.openSubgraphWalk_exists_graphWalk
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) {x y : V}
    (q : (P.openSubgraph omega).Walk x y) :
    ∃ qG : P.graph.Walk x y,
      qG.support = q.support ∧
      ∀ {u v : V}, s(u, v) ∈ qG.edges → omega s(u, v) = true := by
  have hle : P.openSubgraph omega ≤ P.graph := by
    intro u v huv
    exact huv.1
  have hedge : ∀ e, e ∈ q.edges → e ∈ P.graph.edgeSet := by
    intro e he
    exact SimpleGraph.edgeSet_mono hle (q.edges_subset_edgeSet he)
  let qG := q.transfer P.graph hedge
  refine ⟨qG, by simp [qG], ?_⟩
  intro u v huv
  have huv' : s(u, v) ∈ q.edges := by
    simpa [qG] using huv
  have hadj := q.adj_of_mem_edges huv'
  exact hadj.2


end StatMech.FK.PeriodicPlanar
