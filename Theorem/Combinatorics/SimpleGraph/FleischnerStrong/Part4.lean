/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.Combinatorics.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.Contraction
import Lemma.SimpleGraph.EdgeIndexedMultigraph
import Lemma.SimpleGraph.Riha
import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
import Def.Combinatorics.SimpleGraph.Riha
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.ZMod.Basic
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part7
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/

/-! ## CycleComplement -/


namespace SimpleGraph

namespace Walk

attribute [instance] ComponentTrailCover.edge_finite

theorem nontrivialCoverEnds_good_eq [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (e : CycleCoverEdge p) (hgood : IsGoodCycleCoverEdge e)
    (a b : c.componentVertices D) (he : (e : Sym2 _) = s(some a, some b)) :
    nontrivialCoverEnds D hp hfirst hlast
      (Sum.inl (⟨e, hgood⟩ : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e})) =
        s((a : V), (b : V)) := by
  let f : Option (c.componentVertices D) → V := fun z ↦ z.elim a Subtype.val
  have hpair := he.symm.trans (goodCycleCoverEdge_eq ⟨e, hgood⟩)
  have hmapped := congrArg (Sym2.map f) hpair
  simpa [nontrivialCoverEnds, f] using hmapped.symm

theorem IsGoodCycleCoverEdge.adj_of_eq {S : Set V}
    {p : (G.contractOutside S).square.Walk none none} (e : CycleCoverEdge p)
    (hgood : IsGoodCycleCoverEdge e) (a b : S)
    (he : (e : Sym2 (Option S)) = s(some a, some b)) : G.square.Adj a b := by
  let g : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e} := ⟨e, hgood⟩
  let f : Option S → V := fun z ↦ z.elim a Subtype.val
  have hpair := he.symm.trans (goodCycleCoverEdge_eq g)
  have hmapped : s((a : V), (b : V)) =
      s((goodCycleCoverLeft g : V), (goodCycleCoverRight g : V)) := by
    simpa [f] using congrArg (Sym2.map f) hpair
  apply G.square.mem_edgeSet.mp
  rw [hmapped]
  exact G.square.mem_edgeSet.mpr (goodCycleCoverEdge_adj g)

theorem reachable_cycle_of_cycle_subwalk [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D)
    (q : (G.contractOutside (c.componentVertices D)).square.Walk (some d) none)
    (hq : ∀ e ∈ q.edges, e ∈ p.edges) :
    ∃ w ∈ c.support,
      (nontrivialCoverMultigraph D hp hfirst hlast).underlying.Reachable d w := by
  cases hqdef : q with
  | @cons _ z _ hz q' =>
      have hedge_mem : s(some d, z) ∈ p.edges := by
        apply hq
        rw [hqdef, SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_self
      let e : CycleCoverEdge p := cycleCoverEdgeOfMem p hedge_mem
      cases z with
      | none =>
          have hnone : none ∈ (e : Sym2 (Option (c.componentVertices D))) := by
            exact Sym2.mem_iff.mpr (Or.inr rfl)
          let i : BadCycleIncidence p :=
            ⟨e, d, Sym2.mem_iff.mpr (Or.inl rfl),
              IsGoodCycleCoverEdge.not_of_none_mem e hnone⟩
          refine ⟨i.attachment D hp hfirst hlast,
            i.attachment_mem D hp hfirst hlast, ?_⟩
          apply Adj.reachable
          apply (nontrivialCoverMultigraph D hp hfirst hlast).underlying_adj.mpr
          exact ⟨Sum.inr i, rfl⟩
      | some d' =>
          by_cases hgood : G.square.Adj d d'
          · have heq : (e : Sym2 (Option (c.componentVertices D))) =
                s(some d, some d') := rfl
            have hgood_edge : IsGoodCycleCoverEdge e := ⟨d, d', heq, hgood⟩
            let g : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e} :=
              ⟨e, hgood_edge⟩
            have hadj : (nontrivialCoverMultigraph D hp hfirst hlast).underlying.Adj d d' := by
              apply (nontrivialCoverMultigraph D hp hfirst hlast).underlying_adj.mpr
              exact ⟨Sum.inl g,
                nontrivialCoverEnds_good_eq D hp hfirst hlast e hgood_edge d d' heq⟩
            have htail : ∀ f ∈ q'.edges, f ∈ p.edges := by
              intro f hf
              apply hq f
              rw [hqdef, SimpleGraph.Walk.edges_cons]
              exact List.mem_cons_of_mem _ hf
            obtain ⟨w, hwc, hw⟩ :=
              reachable_cycle_of_cycle_subwalk D hp hfirst hlast d' q' htail
            exact ⟨w, hwc, hadj.reachable.trans hw⟩
          · have hnot_good : ¬IsGoodCycleCoverEdge e := by
              intro h
              exact hgood (IsGoodCycleCoverEdge.adj_of_eq e h d d' rfl)
            let i : BadCycleIncidence p :=
              ⟨e, d, Sym2.mem_iff.mpr (Or.inl rfl), hnot_good⟩
            refine ⟨i.attachment D hp hfirst hlast,
              i.attachment_mem D hp hfirst hlast, ?_⟩
            apply Adj.reachable
            apply (nontrivialCoverMultigraph D hp hfirst hlast).underlying_adj.mpr
            exact ⟨Sum.inr i, rfl⟩
termination_by q.length
decreasing_by
  rw [hqdef, SimpleGraph.Walk.length_cons]
  omega

theorem nontrivialCoverMultigraph_reachable_cycle [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) :
    ∃ w ∈ c.support,
      (nontrivialCoverMultigraph D hp hfirst hlast).underlying.Reachable d w := by
  let r := p.rotate (some d) (hp.mem_support (some d))
  have hnone : none ∈ r.support := by
    rw [p.mem_support_rotate_iff]
    exact hp.mem_support none
  let q := r.takeUntil none hnone
  have hq : ∀ e ∈ q.edges, e ∈ p.edges := by
    intro e he
    have her : e ∈ r.edges := r.edges_takeUntil_subset_edges hnone he
    exact (p.rotate_edges (some d) (hp.mem_support (some d))).mem_iff.mp her
  exact reachable_cycle_of_cycle_subwalk D hp hfirst hlast d q hq

/-- A strong Hamiltonian cycle in a nontrivial component contraction yields the Step A trail
cover for that component. -/
theorem ComponentTrailCover.exists_of_contractOutside_strongCycle
    [Finite V] [DecidableEq V] {c : G.Walk x x}
    (D : c.outsideGraph.ConnectedComponent) [Fintype (c.componentVertices D)]
    (hstrong : (G.contractOutside (c.componentVertices D)).HasStrongSquareCycle none) :
    Nonempty (c.ComponentTrailCover D) := by
  classical
  obtain ⟨p, hp, hfirst, hlast⟩ := hstrong
  let M := nontrivialCoverMultigraph D hp hfirst hlast
  refine ⟨{
    Edge := NontrivialCoverEdge p
    edge_finite := nontrivialCoverEdgeFinite
    multigraph := M
    square_adj := nontrivialCoverEnds_square_adj D hp hfirst hlast
    meets_component := nontrivialCoverEnds_meets_component D hp hfirst hlast
    endpoints_mem := nontrivialCoverEnds_endpoints_mem D hp hfirst hlast
    cycle_edge := nontrivialCoverEnds_cycle_edge D hp hfirst hlast
    degree_eq_two := ?_
    reachable_cycle := ?_ }⟩
  · intro v hv
    let d : c.componentVertices D := ⟨v, hv⟩
    exact nontrivialCoverMultigraph_degree_eq_two D hp hfirst hlast d
  · intro v hv
    let d : c.componentVertices D := ⟨v, hv⟩
    exact nontrivialCoverMultigraph_reachable_cycle D hp hfirst hlast d

end Walk
end SimpleGraph
