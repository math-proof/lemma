/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import sympy.atlas.Combinatorics.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.Contraction
import Lemma.SimpleGraph.EdgeIndexedMultigraph
import Lemma.SimpleGraph.Riha
import sympy.atlas.Combinatorics.SimpleGraph.VertexConnectivity
import sympy.atlas.Combinatorics.SimpleGraph.Contraction
import sympy.atlas.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
import sympy.atlas.Combinatorics.SimpleGraph.Riha
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.ZMod.Basic

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

variable {V : Type*} {G : SimpleGraph V} {x : V}

/-- The edge positions of a cycle are in bijection with its support vertices. -/
private noncomputable def IsCycle.finLengthEquivSupport {c : G.Walk x x}
    (hc : c.IsCycle) : Fin c.length ≃ {v // v ∈ c.support} := by
  classical
  have hlength : c.support.dropLast.length = c.length := by
    rw [List.length_dropLast, c.length_support]
    omega
  let eSupport : {v // v ∈ c.support.dropLast} ≃ {v // v ∈ c.support} := {
    toFun := fun v ↦ ⟨v, (hc.mem_dropLast_support_iff v).mp v.property⟩
    invFun := fun v ↦ ⟨v, (hc.mem_dropLast_support_iff v).mpr v.property⟩
    left_inv := fun _ ↦ Subtype.ext rfl
    right_inv := fun _ ↦ Subtype.ext rfl }
  exact (finCongr hlength.symm).trans
    ((hc.nodup_dropLast_support.getEquiv).trans eSupport)

/-- The graph induced by the vertices outside a closed walk. -/
private def outsideGraph (c : G.Walk x x) : SimpleGraph {v // v ∉ c.support} :=
  G.induce {v | v ∉ c.support}

/-- The original vertices belonging to one connected component outside a closed walk. -/
private def componentVertices (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) : Set V :=
  Subtype.val '' D.supp

private def componentGraphHom (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) :
    D.toSimpleGraph →g G.induce (c.componentVertices D) where
  toFun w := ⟨w.1.1, w.1, w.2, rfl⟩
  map_rel' := by
    intro u v huv
    exact huv
end Walk
end SimpleGraph
namespace SimpleGraph
namespace Walk
end Walk
end SimpleGraph
namespace SimpleGraph
end SimpleGraph
namespace SimpleGraph

/-- A rooted cyclic listing witnessing a Hamiltonian cycle in the square, with original-graph
edges at the root. -/
private structure StrongSquareCycleListing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) where
  vertices : List V
  first : V
  last : V
  frontRest : List V
  backRest : List V
  front_shape : vertices = x :: first :: frontRest
  back_shape : vertices = backRest ++ [last, x]
  four_le_length : 4 ≤ vertices.length
  square_chain : vertices.IsChain G.square.Adj
  tail_nodup : vertices.tail.Nodup
  mem_tail : ∀ v, v ∈ vertices.tail
  first_adj : G.Adj x first
  last_adj : G.Adj last x
end SimpleGraph
namespace SimpleGraph
namespace Walk

/-- A finite indexed multigraph covering one component outside a cycle. -/
private structure ComponentTrailCover (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) where
  /-- Edge identities, including identities for parallel copies. -/
  Edge : Type u
  edge_finite : Finite Edge
  /-- The indexed multigraph carried by the cover. -/
  multigraph : EdgeIndexedMultigraph V Edge
  /-- Every cover edge is an edge of the square. -/
  square_adj : ∀ e, multigraph.ends e ∈ G.square.edgeSet
  /-- Every cover edge has an endpoint in the component. -/
  meets_component : ∀ e, ∃ v ∈ c.componentVertices D, v ∈ multigraph.ends e
  /-- The other endpoints lie either in the component or on the cycle. -/
  endpoints_mem : ∀ e v, v ∈ multigraph.ends e →
    v ∈ c.componentVertices D ∨ v ∈ c.support
  /-- Edges incident with the cycle are original graph edges. -/
  cycle_edge : ∀ e u v, multigraph.ends e = s(u, v) →
    (u ∈ c.support ∨ v ∈ c.support) → G.Adj u v
  /-- Each component vertex has degree two in the cover. -/
  degree_eq_two : ∀ v ∈ c.componentVertices D, multigraph.degree v = 2
  /-- Each component vertex is connected by cover edges to the cycle. -/
  reachable_cycle : ∀ v ∈ c.componentVertices D,
    ∃ w ∈ c.support, multigraph.underlying.Reachable v w

attribute [instance] ComponentTrailCover.edge_finite

private def singletonCoverEnds (u a b : V) (i : Fin 2) : Sym2 V :=
  if i = 0 then s(u, a) else s(u, b)

private abbrev CycleCoverEdge {S : Set V}
    (p : (G.contractOutside S).square.Walk none none) :=
  p.toSubgraph.spanningCoe.edgeSet

private def IsGoodCycleCoverEdge {S : Set V}
    {p : (G.contractOutside S).square.Walk none none} (e : CycleCoverEdge p) : Prop :=
  ∃ a b : S, (e : Sym2 (Option S)) = s(some a, some b) ∧ G.square.Adj a b

private structure BadCycleIncidence {S : Set V}
    (p : (G.contractOutside S).square.Walk none none) where
  edge : CycleCoverEdge p
  vertex : S
  mem_edge : some vertex ∈ (edge : Sym2 (Option S))
  not_good : ¬IsGoodCycleCoverEdge edge

private abbrev NontrivialCoverEdge {S : Set V}
    (p : (G.contractOutside S).square.Walk none none) :=
  {e : CycleCoverEdge p // IsGoodCycleCoverEdge e} ⊕ BadCycleIncidence p

private def NontrivialCoverEdge.sourceCycleEdge {S : Set V}
    {p : (G.contractOutside S).square.Walk none none} :
    NontrivialCoverEdge p → CycleCoverEdge p
  | Sum.inl e => e.1
  | Sum.inr i => i.edge

private noncomputable def goodCycleCoverLeft {S : Set V}
    {p : (G.contractOutside S).square.Walk none none}
    (e : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e}) : S :=
  e.property.choose

private noncomputable def goodCycleCoverRight {S : Set V}
    {p : (G.contractOutside S).square.Walk none none}
    (e : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e}) : S :=
  e.property.choose_spec.choose

private theorem goodCycleCoverEdge_eq {S : Set V}
    {p : (G.contractOutside S).square.Walk none none}
    (e : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e}) :
    (e.1 : Sym2 (Option S)) =
      s(some (goodCycleCoverLeft e), some (goodCycleCoverRight e)) :=
  e.property.choose_spec.choose_spec.1

private theorem goodCycleCoverEdge_adj {S : Set V}
    {p : (G.contractOutside S).square.Walk none none}
    (e : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e}) :
    G.square.Adj (goodCycleCoverLeft e) (goodCycleCoverRight e) :=
  e.property.choose_spec.choose_spec.2

private noncomputable def BadCycleIncidence.attachment [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (i : BadCycleIncidence p) : V :=
  (i.exists_attachment D hp hfirst hlast).choose

private noncomputable def nontrivialCoverEnds [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none) :
    NontrivialCoverEdge p → Sym2 V
  | Sum.inl e => s(goodCycleCoverLeft e, goodCycleCoverRight e)
  | Sum.inr i => s(i.vertex, i.attachment D hp hfirst hlast)

private theorem nontrivialCoverEnds_square_adj [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (e : NontrivialCoverEdge p) :
    nontrivialCoverEnds D hp hfirst hlast e ∈ G.square.edgeSet := by
  cases e with
  | inl e => exact G.square.mem_edgeSet.mpr (goodCycleCoverEdge_adj e)
  | inr i =>
      have hi := i.adj_attachment D hp hfirst hlast
      exact G.square.mem_edgeSet.mpr ⟨G.ne_of_adj hi, Or.inl hi⟩

private noncomputable def nontrivialCoverMultigraph [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none) :
    EdgeIndexedMultigraph V (NontrivialCoverEdge p) where
  ends := nontrivialCoverEnds D hp hfirst hlast
  loopless := by
    intro e v hev
    have hedge := nontrivialCoverEnds_square_adj D hp hfirst hlast e
    rw [hev] at hedge
    exact G.square.loopless.irrefl v (G.square.mem_edgeSet.mp hedge)

private noncomputable def cycleIncidenceToCover [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) :
    (p.toSubgraph.spanningCoe.incidenceSet (some d)) →
      {e : NontrivialCoverEdge p //
        (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e} := by
  intro q
  let e : CycleCoverEdge p := ⟨q.1, q.2.1⟩
  by_cases hgood : IsGoodCycleCoverEdge e
  · let g : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e} := ⟨e, hgood⟩
    refine ⟨Sum.inl g, ?_⟩
    have hd := q.2.2
    rw [goodCycleCoverEdge_eq g] at hd
    rcases Sym2.mem_iff.mp hd with hd | hd
    · exact Sym2.mem_iff.mpr (Or.inl (congrArg Subtype.val (Option.some.inj hd)))
    · exact Sym2.mem_iff.mpr (Or.inr (congrArg Subtype.val (Option.some.inj hd)))
  · let i : BadCycleIncidence p := ⟨e, d, q.2.2, hgood⟩
    exact ⟨Sum.inr i, Sym2.mem_iff.mpr (Or.inl rfl)⟩

private noncomputable def coverIncidenceToCycle [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) :
    {e : NontrivialCoverEdge p //
      (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e} →
      p.toSubgraph.spanningCoe.incidenceSet (some d) := by
  rintro ⟨e, hde⟩
  cases e with
  | inl e =>
      refine ⟨e.1, e.1.property, ?_⟩
      rw [goodCycleCoverEdge_eq e]
      rcases Sym2.mem_iff.mp hde with hd | hd
      · exact Sym2.mem_iff.mpr (Or.inl (congrArg some (Subtype.ext hd)))
      · exact Sym2.mem_iff.mpr (Or.inr (congrArg some (Subtype.ext hd)))
  | inr i =>
      refine ⟨i.edge.1, i.edge.property, ?_⟩
      rcases Sym2.mem_iff.mp hde with hd | hd
      · have hdi : d = i.vertex := Subtype.ext hd
        exact hdi ▸ i.mem_edge
      · exfalso
        have hd_out := c.componentVertices_subset_compl D d.property
        exact hd_out (hd ▸ i.attachment_mem D hp hfirst hlast)

private theorem cycleIncidenceToCover_source [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D)
    (q : p.toSubgraph.spanningCoe.incidenceSet (some d)) :
    (cycleIncidenceToCover D hp hfirst hlast d q).1.sourceCycleEdge =
      (⟨q.1, q.2.1⟩ : CycleCoverEdge p) := by
  apply Subtype.ext
  simp only [cycleIncidenceToCover]
  split <;> rfl

private theorem coverIncidenceToCycle_val [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D)
    (q : {e : NontrivialCoverEdge p //
      (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e}) :
    ((coverIncidenceToCycle D hp hfirst hlast d q :
      p.toSubgraph.spanningCoe.incidenceSet (some d)) : Sym2 (Option _)) =
      (q.1.sourceCycleEdge : Sym2 (Option (c.componentVertices D))) := by
  rcases q with ⟨e, he⟩
  cases e <;> rfl

private theorem coverIncidenceToCycle_cycleIncidenceToCover [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D)
    (q : p.toSubgraph.spanningCoe.incidenceSet (some d)) :
    coverIncidenceToCycle D hp hfirst hlast d
      (cycleIncidenceToCover D hp hfirst hlast d q) = q := by
  apply Subtype.ext
  rw [coverIncidenceToCycle_val, cycleIncidenceToCover_source]

private theorem badCycleIncidence_vertex_eq_of_mem [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) (i : BadCycleIncidence p)
    (hde : (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast (Sum.inr i)) :
    d = i.vertex := by
  rcases Sym2.mem_iff.mp hde with hd | hd
  · exact Subtype.ext hd
  · exfalso
    have hd_out := c.componentVertices_subset_compl D d.property
    exact hd_out (hd ▸ i.attachment_mem D hp hfirst hlast)

private theorem cycleIncidenceToCover_coverIncidenceToCycle [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D)
    (q : {e : NontrivialCoverEdge p //
      (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e}) :
    cycleIncidenceToCover D hp hfirst hlast d
      (coverIncidenceToCycle D hp hfirst hlast d q) = q := by
  rcases q with ⟨e, he⟩
  apply Subtype.ext
  cases e with
  | inl g =>
      simp only [coverIncidenceToCycle, cycleIncidenceToCover]
      simp [g.property]
  | inr i =>
      have hdi := badCycleIncidence_vertex_eq_of_mem D hp hfirst hlast d i he
      subst d
      simp only [coverIncidenceToCycle, cycleIncidenceToCover]
      simp [i.not_good]

private noncomputable def cycleCoverIncidenceEquiv [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) :
    p.toSubgraph.spanningCoe.incidenceSet (some d) ≃
      {e : NontrivialCoverEdge p //
        (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e} where
  toFun := cycleIncidenceToCover D hp hfirst hlast d
  invFun := coverIncidenceToCycle D hp hfirst hlast d
  left_inv := coverIncidenceToCycle_cycleIncidenceToCover D hp hfirst hlast d
  right_inv := cycleIncidenceToCover_coverIncidenceToCycle D hp hfirst hlast d

private def cycleCoverEdgeOfMem {S : Set V}
    (p : (G.contractOutside S).square.Walk none none) {a b : Option S}
    (he : s(a, b) ∈ p.edges) : CycleCoverEdge p := by
  refine ⟨s(a, b), ?_⟩
  change s(a, b) ∈ p.toSubgraph.spanningCoe.edgeSet
  rw [Subgraph.edgeSet_spanningCoe, p.mem_edges_toSubgraph]
  exact he

private theorem nontrivialCoverEnds_good_eq [DecidableEq V]
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

private theorem IsGoodCycleCoverEdge.adj_of_eq {S : Set V}
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

private theorem reachable_cycle_of_cycle_subwalk [DecidableEq V]
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

private theorem nontrivialCoverMultigraph_reachable_cycle [DecidableEq V]
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
private theorem ComponentTrailCover.exists_of_contractOutside_strongCycle
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

/-! ## CycleTrailSystem -/

namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

/-- Edge identities in the union of a cycle and one trail cover for every outside component. -/
private abbrev TrailSystemEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :=
  ULift.{u} (Fin c.length) ⊕ Σ D, (cover D).Edge

private instance trailSystemEdgeFinite [Finite V] (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :
    Finite (c.TrailSystemEdge cover) := by
  let _ : ∀ D : c.outsideGraph.ConnectedComponent, Finite (cover D).Edge :=
    fun D ↦ (cover D).edge_finite
  infer_instance

/-- The indexed multigraph formed by the cycle and all outside-component trail covers. -/
private noncomputable def trailSystemMultigraph (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :
    EdgeIndexedMultigraph V (c.TrailSystemEdge cover) where
  ends
    | Sum.inl i => s(c.getVert i.down, c.getVert (i.down + 1))
    | Sum.inr e => (cover e.1).multigraph.ends e.2
  loopless := by
    intro e v he
    cases e with
    | inl i =>
        have hadj := c.adj_getVert_succ i.down.isLt
        have hedge : s(c.getVert i.down, c.getVert (i.down + 1)) ∈ G.edgeSet :=
          G.mem_edgeSet.mpr hadj
        change s(c.getVert i.down, c.getVert (i.down + 1)) = s(v, v) at he
        rw [he] at hedge
        exact G.loopless.irrefl v (G.mem_edgeSet.mp hedge)
    | inr e => exact (cover e.1).multigraph.loopless e.2 v he

private def outsideComponent (c : G.Walk x x) {v : V} (hv : v ∉ c.support) :
    c.outsideGraph.ConnectedComponent :=
  c.outsideGraph.connectedComponentMk ⟨v, hv⟩

private theorem component_eq_outsideComponent (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) {v : V} (hv : v ∉ c.support)
    (hvD : v ∈ c.componentVertices D) : outsideComponent c hv = D := by
  obtain ⟨hv', hD⟩ := (c.mem_componentVertices_iff D v).mp hvD
  simpa [outsideComponent] using hD

private theorem mem_support_of_mem_cycle_edge (c : G.Walk x x)
    (i : Fin c.length) {v : V}
    (hv : v ∈ s(c.getVert i, c.getVert (i + 1))) : v ∈ c.support := by
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact c.getVert_mem_support i
  · exact c.getVert_mem_support (i + 1)

private def componentIncidenceToTrailSystem (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    {v : V} (hv : v ∉ c.support) :
    {e : (cover (outsideComponent c hv)).Edge |
      (cover (outsideComponent c hv)).multigraph.Inc v e} →
      {e : c.TrailSystemEdge cover | (c.trailSystemMultigraph cover).Inc v e} :=
  fun e ↦ ⟨Sum.inr ⟨outsideComponent c hv, e.1⟩, e.2⟩

private noncomputable def trailSystemIncidenceToComponent (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    {v : V} (hv : v ∉ c.support) :
    {e : c.TrailSystemEdge cover | (c.trailSystemMultigraph cover).Inc v e} →
      {e : (cover (outsideComponent c hv)).Edge |
        (cover (outsideComponent c hv)).multigraph.Inc v e} := by
  rintro ⟨e, hve⟩
  cases e with
  | inl i =>
      exfalso
      exact hv (mem_support_of_mem_cycle_edge c i.down hve)
  | inr e =>
      rcases e with ⟨D, e⟩
      have hvD : v ∈ c.componentVertices D := by
        rcases (cover D).endpoints_mem e v hve with hvD | hvc
        · exact hvD
        · exact False.elim (hv hvc)
      have hD := component_eq_outsideComponent c D hv hvD
      subst D
      exact ⟨e, hve⟩

private noncomputable def trailSystemIncidenceEquiv (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    {v : V} (hv : v ∉ c.support) :
    {e : (cover (outsideComponent c hv)).Edge |
      (cover (outsideComponent c hv)).multigraph.Inc v e} ≃
      {e : c.TrailSystemEdge cover | (c.trailSystemMultigraph cover).Inc v e} where
  toFun := componentIncidenceToTrailSystem c cover hv
  invFun := trailSystemIncidenceToComponent c cover hv
  left_inv := by
    intro e
    apply Subtype.ext
    simp [componentIncidenceToTrailSystem, trailSystemIncidenceToComponent]
  right_inv := by
    rintro ⟨e, he⟩
    apply Subtype.ext
    cases e with
    | inl i => exact False.elim (hv (mem_support_of_mem_cycle_edge c i.down he))
    | inr e =>
        rcases e with ⟨D, e⟩
        have hvD : v ∈ c.componentVertices D := by
          rcases (cover D).endpoints_mem e v he with hvD | hvc
          · exact hvD
          · exact False.elim (hv hvc)
        have hD := component_eq_outsideComponent c D hv hvD
        subst D
        rfl
end Walk
end SimpleGraph

/-- A choice of at most one copied edge at every position of a cyclic degree sequence. -/
private structure CyclicParityCompletion {n : ℕ} [NeZero n] (d : Fin n → ℕ) where
  /-- The number of extra copies, always zero or one. -/
  copies : Fin n → ℕ
  copies_lt_two : ∀ i, copies i < 2
  /-- Position zero is the protected edge. -/
  copies_zero : copies 0 = 0
  /-- The two incident copy choices correct the parity at each cyclic vertex. -/
  even_at : ∀ i, Even (d i + copies (i - 1) + copies i)

/-- Sum of the degrees strictly after position zero and at most position `i`. -/
private def cyclicPrefix {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : ℕ :=
  ∑ j : Fin i.val,
    d ⟨j.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt j.isLt) i.isLt⟩

private theorem cyclicPrefix_zero {n : ℕ} [NeZero n] (d : Fin n → ℕ) :
    cyclicPrefix d 0 = 0 := by
  simp [cyclicPrefix]

private theorem cyclicPrefix_eq_sub_one_add {n : ℕ} [NeZero n]
    (d : Fin n → ℕ) (i : Fin n) (hi : i ≠ 0) :
    cyclicPrefix d i = cyclicPrefix d (i - 1) + d i := by
  rcases i with ⟨i, hiLt⟩
  cases i with
  | zero => exact (hi rfl).elim
  | succ k =>
      let p : Fin n := ⟨k, lt_trans (Nat.lt_succ_self k) hiLt⟩
      have hp : (⟨k + 1, hiLt⟩ - 1 : Fin n) = p := by
        apply Fin.ext
        rw [Fin.val_sub_one_of_ne_zero hi]
        change k + 1 - 1 = k
        omega
      rw [hp]
      simp only [cyclicPrefix, p, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

private theorem zero_add_cyclicPrefix_last {m : ℕ} (d : Fin (m + 1) → ℕ) :
    d 0 + cyclicPrefix d (Fin.last m) = ∑ i, d i := by
  rw [Fin.sum_univ_succ]
  simp only [cyclicPrefix, Fin.val_last]
  congr

/-- The canonical parity completion, obtained by taking prefix parities away from position
zero. -/
private noncomputable def cyclicParityCompletion {n : ℕ} [NeZero n]
    (d : Fin n → ℕ) (hsum : Even (∑ i, d i)) : CyclicParityCompletion d where
  copies i := cyclicPrefix d i % 2
  copies_lt_two i := Nat.mod_lt _ (by omega)
  copies_zero := by simp [cyclicPrefix_zero]
  even_at := by
    intro i
    by_cases hi : i = 0
    · subst i
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      have hprev : (0 - 1 : Fin (m + 1)) = Fin.last m := by
        cases m with
        | zero =>
            apply Fin.ext
            rfl
        | succ k =>
            apply Fin.ext
            simp
      rw [hprev, cyclicPrefix_zero]
      rw [← zero_add_cyclicPrefix_last d] at hsum
      rw [Nat.even_iff] at hsum ⊢
      omega
    · rw [cyclicPrefix_eq_sub_one_add d i hi, Nat.even_iff]
      omega

/-! ## CycleCopies -/

namespace SimpleGraph

namespace Walk

variable {V : Type*} {G : SimpleGraph V} {x : V}

/-- Edge identities for prescribed copies of edges of a closed walk. -/
private abbrev CycleCopyEdge (c : G.Walk x x) [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :=
  Σ i : Fin c.length, Fin (q.copies i)

private instance cycleCopyEdgeFinite (c : G.Walk x x) [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :
    Finite (c.CycleCopyEdge q) := by
  infer_instance

/-- The indexed multigraph of the prescribed parallel cycle-edge copies. -/
private def cycleCopyMultigraph (c : G.Walk x x) [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :
    EdgeIndexedMultigraph V (c.CycleCopyEdge q) where
  ends e := s(c.getVert e.1, c.getVert (e.1.val + 1))
  loopless := by
    intro e v he
    have hadj := c.adj_getVert_succ e.1.isLt
    apply G.loopless.irrefl v
    apply G.mem_edgeSet.mp
    rw [← he]
    exact G.mem_edgeSet.mpr hadj

private theorem cycleCopyMultigraph_inc_getVert_iff {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) (e : c.CycleCopyEdge q) :
    (c.cycleCopyMultigraph q).Inc (c.getVert i) e ↔
      e.1 = i ∨ e.1 = i - 1 := by
  change c.getVert i ∈ s(c.getVert e.1, c.getVert (e.1.val + 1)) ↔ _
  rw [hc.getVert_succ_eq_add_one]
  constructor
  · intro he
    rcases Sym2.mem_iff.mp he with he | he
    · exact Or.inl (hc.getVert_injective_fin he.symm)
    · have hi : i = e.1 + 1 := hc.getVert_injective_fin he
      exact Or.inr (eq_sub_iff_add_eq.mpr hi.symm)
  · rintro (rfl | he)
    · exact Sym2.mem_iff.mpr (Or.inl rfl)
    · apply Sym2.mem_iff.mpr
      right
      apply congrArg c.getVert
      rw [he, sub_add_cancel]

private theorem no_cover_inc_bound_vertex [Finite V] (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    (i : Fin c.length) (hbound : c.IsBoundVertex (c.getVert i))
    (D : c.outsideGraph.ConnectedComponent) (f : (cover D).Edge) :
    ¬(c.trailSystemMultigraph cover).Inc (c.getVert i) (Sum.inr ⟨D, f⟩) := by
  intro hinc
  obtain ⟨z, hzD, hzinc⟩ := (cover D).meets_component f
  have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
  have hne : c.getVert i ≠ z := by
    intro h
    exact hzout (h ▸ c.getVert_mem_support i)
  change c.getVert i ∈ (cover D).multigraph.ends f at hinc
  have hends : (cover D).multigraph.ends f = s(c.getVert i, z) :=
    (Sym2.mem_and_mem_iff hne).mp ⟨hinc, hzinc⟩
  have hadj : G.Adj (c.getVert i) z :=
    (cover D).cycle_edge f _ _ hends (Or.inl (c.getVert_mem_support i))
  exact hzout (hbound.2 hadj)

private noncomputable def boundIncidenceEquiv [Finite V] (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    (i : Fin c.length) (hbound : c.IsBoundVertex (c.getVert i)) :
    {e : c.TrailSystemEdge cover //
      (c.trailSystemMultigraph cover).Inc (c.getVert i) e} ≃ Fin 2 := by
  let embed : Fin 2 → {e : c.TrailSystemEdge cover //
      (c.trailSystemMultigraph cover).Inc (c.getVert i) e} := fun k ↦
    if hk : k = 0 then
      ⟨Sum.inl (ULift.up i), by
        change c.getVert i ∈ s(c.getVert i, c.getVert (i + 1))
        simp⟩
    else
      ⟨Sum.inl (ULift.up (i - 1)), by
        simp only [EdgeIndexedMultigraph.Inc, trailSystemMultigraph]
        rw [hc.getVert_succ_eq_add_one, sub_add_cancel]
        exact Sym2.mem_iff.mpr (Or.inr rfl)⟩
  have hinj : Function.Injective embed := by
    intro a b hab
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · exact hb.symm
      · have hval := congrArg (fun e ↦ e.1) hab
        simp only [embed, dite_eq_left rfl, dite_eq_right hb] at hval
        have hindex : i = i - 1 := by
          simpa only [Sum.inl.injEq, ULift.up_inj] using hval
        exact False.elim (hc.sub_one_ne i hindex.symm)
    · have ha1 : a = 1 := Fin.eq_one_of_ne_zero a ha
      subst a
      by_cases hb : b = 0
      · subst b
        have hval := congrArg (fun e ↦ e.1) hab
        simp only [embed, dite_eq_left rfl,
          dite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at hval
        have hindex : i - 1 = i := by
          simpa only [Sum.inl.injEq, ULift.up_inj] using hval
        exact False.elim (hc.sub_one_ne i hindex)
      · exact (Fin.eq_one_of_ne_zero b hb).symm
  have hsurj : Function.Surjective embed := by
    rintro ⟨e, he⟩
    cases e with
    | inr e =>
        exact False.elim
          (no_cover_inc_bound_vertex c cover i hbound e.1 e.2 he)
    | inl j =>
        change c.getVert i ∈
          s(c.getVert j.down, c.getVert (j.down + 1)) at he
        rcases Sym2.mem_iff.mp he with he | he
        · have hji : j.down = i := hc.getVert_injective_fin he.symm
          refine ⟨0, ?_⟩
          apply Subtype.ext
          change Sum.inl (ULift.up i) = Sum.inl j
          congr
          exact hji.symm
        · rw [hc.getVert_succ_eq_add_one] at he
          have hi : i = j.down + 1 := hc.getVert_injective_fin he
          have hji : j.down = i - 1 := eq_sub_iff_add_eq.mpr hi.symm
          refine ⟨1, ?_⟩
          apply Subtype.ext
          change Sum.inl (ULift.up (i - 1)) = Sum.inl j
          congr
          exact hji.symm
  exact (Equiv.ofBijective embed ⟨hinj, hsurj⟩).symm

private noncomputable def cycleCopyIncidenceTo {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    {e : c.CycleCopyEdge q // (c.cycleCopyMultigraph q).Inc (c.getVert i) e} →
      Fin (q.copies (i - 1)) ⊕ Fin (q.copies i) := by
  rintro ⟨⟨j, k⟩, he⟩
  by_cases hji : j = i
  · subst j
    exact Sum.inr k
  · have hjp : j = i - 1 :=
      (cycleCopyMultigraph_inc_getVert_iff hc q i ⟨j, k⟩).mp he |>.resolve_left hji
    subst j
    exact Sum.inl k

private def cycleCopyIncidenceFrom {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    Fin (q.copies (i - 1)) ⊕ Fin (q.copies i) →
      {e : c.CycleCopyEdge q // (c.cycleCopyMultigraph q).Inc (c.getVert i) e}
  | Sum.inl k =>
      ⟨⟨i - 1, k⟩, (cycleCopyMultigraph_inc_getVert_iff hc q i _).mpr (Or.inr rfl)⟩
  | Sum.inr k =>
      ⟨⟨i, k⟩, (cycleCopyMultigraph_inc_getVert_iff hc q i _).mpr (Or.inl rfl)⟩

private theorem cycleCopyIncidence_leftInverse {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    Function.LeftInverse (cycleCopyIncidenceFrom hc q i)
      (cycleCopyIncidenceTo hc q i) := by
  rintro ⟨⟨j, k⟩, he⟩
  by_cases hji : j = i
  · subst j
    simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom]
  · have hjp : j = i - 1 :=
      (cycleCopyMultigraph_inc_getVert_iff hc q i ⟨j, k⟩).mp he |>.resolve_left hji
    subst j
    simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom, hc.sub_one_ne i]

private theorem cycleCopyIncidence_rightInverse {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    Function.RightInverse (cycleCopyIncidenceFrom hc q i)
      (cycleCopyIncidenceTo hc q i) := by
  intro e
  cases e with
  | inl k =>
      simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom, hc.sub_one_ne i]
  | inr k =>
      simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom]

private noncomputable def cycleCopyIncidenceEquiv {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    {e : c.CycleCopyEdge q // (c.cycleCopyMultigraph q).Inc (c.getVert i) e} ≃
      Fin (q.copies (i - 1)) ⊕ Fin (q.copies i) where
  toFun := cycleCopyIncidenceTo hc q i
  invFun := cycleCopyIncidenceFrom hc q i
  left_inv := cycleCopyIncidence_leftInverse hc q i
  right_inv := cycleCopyIncidence_rightInverse hc q i

end Walk
end SimpleGraph
namespace SimpleGraph
namespace Walk
/-- The canonical copy choices that correct the trail-system degrees on a cycle. -/
private noncomputable def cycleEulerizationCompletion [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle) [NeZero c.length]
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :
    CyclicParityCompletion
      (fun i : Fin c.length ↦ (c.trailSystemMultigraph cover).degree (c.getVert i)) :=
  cyclicParityCompletion _ (c.trailSystemMultigraph_cycle_degree_sum_even hc cover)

/-- The Step A trail system together with its parity-correcting cycle-edge copies. -/
private noncomputable def cycleEulerizationMultigraph [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle) [NeZero c.length]
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :=
  (c.trailSystemMultigraph cover).disjointSum
    (c.cycleCopyMultigraph (c.cycleEulerizationCompletion hc cover))
end Walk
end SimpleGraph
namespace SimpleGraph
namespace EdgeIndexedMultigraph

/-- Two adjacent indexed edges to be traversed consecutively. -/
private structure EdgeTransition where
  /-- First edge of the pass. -/
  left : E
  /-- Second edge of the pass. -/
  right : E
  /-- Outer endpoint of the first edge. -/
  before : V
  /-- Common endpoint. -/
  center : V
  /-- Outer endpoint of the second edge. -/
  after : V
  left_ends : M.ends left = s(before, center)
  right_ends : M.ends right = s(center, after)
  before_ne_after : before ≠ after

/-- Select one of the two original edge identities belonging to a transition. -/
private def transitionEdge {T : Type*} (transition : T → M.EdgeTransition) :
    T × Fin 2 → E
  | (t, side) => if side = 0 then (transition t).left else (transition t).right

/-- Original edges not consumed by a forced transition. -/
private abbrev UnpairedTransitionEdge {T : Type*}
    (transition : T → M.EdgeTransition) :=
  {e : E // e ∉ Set.range (M.transitionEdge transition)}

/-- Edge identities after every forced transition is compressed to one temporary edge. -/
private abbrev CompressedTransitionEdge {T : Type*}
    (transition : T → M.EdgeTransition) :=
  M.UnpairedTransitionEdge transition ⊕ T

private instance unpairedTransitionEdgeFinite {T : Type*} [Finite E]
    (transition : T → M.EdgeTransition) :
    Finite (M.UnpairedTransitionEdge transition) :=
  inferInstance

private instance compressedTransitionEdgeFinite {T : Type*} [Finite E] [Finite T]
    (transition : T → M.EdgeTransition) :
    Finite (M.CompressedTransitionEdge transition) :=
  inferInstance

/-- Simultaneously compress a family of forced transitions. -/
private def compressTransitions {T : Type*} (transition : T → M.EdgeTransition) :
    EdgeIndexedMultigraph V (M.CompressedTransitionEdge transition) where
  ends
    | Sum.inl e => M.ends e.1
    | Sum.inr t => s((transition t).before, (transition t).after)
  loopless := by
    intro e v he
    cases e with
    | inl e => exact M.loopless e.1 v he
    | inr t =>
        rcases Sym2.eq_iff.mp he with h | h
        · exact (transition t).before_ne_after (h.1.trans h.2.symm)
        · exact (transition t).before_ne_after (h.1.trans h.2.symm)

private noncomputable def edgePartitionEquiv {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) :
    E ≃ M.UnpairedTransitionEdge transition ⊕ (T × Fin 2) := by
  classical
  exact
    (Equiv.sumCompl (fun e ↦ e ∈ Set.range (M.transitionEdge transition))).symm |>.trans
      (Equiv.sumCongr (Equiv.ofInjective _ hinj).symm (Equiv.refl _)) |>.trans
      (Equiv.sumComm _ _)

private noncomputable def incidenceWeight (v : V) (e : E) : ZMod 2 := by
  classical
  exact if M.Inc v e then 1 else 0

/-- The original edge identities represented by one compressed edge. -/
private def transitionExpansionEdges {T : Type*}
    (transition : T → M.EdgeTransition) :
    M.CompressedTransitionEdge transition → List E
  | Sum.inl e => [e.1]
  | Sum.inr t => [(transition t).left, (transition t).right]

/-- Two edge identities occur consecutively, in either order, in an edge list. -/
private def EdgesAdjacent (a b : E) (l : List E) : Prop :=
  ∃ before after, l = before ++ a :: b :: after ∨
    l = before ++ b :: a :: after

private theorem EdgesAdjacent.cons {a b : E} {l : List E}
    (h : EdgesAdjacent a b l) (e : E) : EdgesAdjacent a b (e :: l) := by
  rcases h with ⟨before, after, h | h⟩
  · exact ⟨e :: before, after, Or.inl (congrArg (e :: ·) h)⟩
  · exact ⟨e :: before, after, Or.inr (congrArg (e :: ·) h)⟩

/-- One expanded transition, together with its edge-list permutation. -/
private structure PrependedTransition [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {a b c : V}
    (e : M.CompressedTransitionEdge transition)
    (he : (M.compressTransitions transition).ends e = s(a, b))
    (q : M.IndexedWalk b c) where
  walk : M.IndexedWalk a c
  edges_perm : walk.edges.Perm (M.transitionExpansionEdges transition e ++ q.edges)
  edges_shape : match e with
    | Sum.inl f => walk.edges = f.1 :: q.edges
    | Sum.inr t => walk.edges = (transition t).left :: (transition t).right :: q.edges ∨
        walk.edges = (transition t).right :: (transition t).left :: q.edges

/-- Expand one compressed edge in front of an already expanded tail. -/
private def prependExpandedTransition [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {a b c : V}
    (e : M.CompressedTransitionEdge transition)
    (he : (M.compressTransitions transition).ends e = s(a, b))
    (q : M.IndexedWalk b c) : M.PrependedTransition transition e he q := by
  cases e with
  | inl e =>
      exact ⟨.cons e.1 he q, List.Perm.refl _, rfl⟩
  | inr t =>
      change s((transition t).before, (transition t).after) = s(a, b) at he
      by_cases ha : a = (transition t).before
      · subst a
        have hb : b = (transition t).after := by
          rcases Sym2.eq_iff.mp he with h | h
          · exact h.2.symm
          · exact False.elim ((transition t).before_ne_after h.2.symm)
        subst b
        exact ⟨.cons (transition t).left (transition t).left_ends
          (.cons (transition t).right (transition t).right_ends q),
          by simp [transitionExpansionEdges], Or.inl rfl⟩
      · have hab : a = (transition t).after ∧ b = (transition t).before := by
          rcases Sym2.eq_iff.mp he with h | h
          · exact False.elim (ha h.1.symm)
          · exact ⟨h.2.symm, h.1.symm⟩
        rcases hab with ⟨hafter, hbefore⟩
        subst a
        subst b
        refine ⟨.cons (transition t).right
          ((transition t).right_ends.trans Sym2.eq_swap)
          (.cons (transition t).left
            ((transition t).left_ends.trans Sym2.eq_swap) q), ?_, Or.inr rfl⟩
        exact List.Perm.swap (transition t).left (transition t).right q.edges

/-- An expanded compressed walk and its canonical edge-list permutation. -/
private structure ExpandedTransitions [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {u v : V}
    (p : (M.compressTransitions transition).IndexedWalk u v) where
  walk : M.IndexedWalk u v
  edges_perm : walk.edges.Perm
    (p.edges.flatMap (M.transitionExpansionEdges transition))
  edges_adjacent : ∀ t, Sum.inr t ∈ p.edges →
    EdgesAdjacent (transition t).left (transition t).right walk.edges

/-- Expand a compressed walk while retaining its edge-list permutation. -/
private def expandTransitionsWithEdges [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {u v : V} :
    (p : (M.compressTransitions transition).IndexedWalk u v) →
      M.ExpandedTransitions transition p
  | .nil w => ⟨.nil w, by simp, by simp⟩
  | .cons e he p =>
      let tail := expandTransitionsWithEdges transition p
      let step := M.prependExpandedTransition transition e he tail.walk
      ⟨step.walk, step.edges_perm.trans (tail.edges_perm.append_left _), by
        intro t ht
        rw [IndexedWalk.edges_cons] at ht
        rcases List.mem_cons.mp ht with het | ht
        · cases e with
          | inl e => simp at het
          | inr t' =>
              have htt : t' = t := Sum.inr.inj het.symm
              subst t'
              rcases step.edges_shape with h | h
              · rw [h]
                exact ⟨[], tail.walk.edges, Or.inl rfl⟩
              · rw [h]
                exact ⟨[], tail.walk.edges, Or.inr rfl⟩
        · have htail := tail.edges_adjacent t ht
          cases e with
          | inl e =>
              rw [step.edges_shape]
              exact htail.cons e.1
          | inr t' =>
              rcases step.edges_shape with h | h
              · rw [h]
                exact (htail.cons (transition t').right).cons
                  (transition t').left
              · rw [h]
                exact (htail.cons (transition t').left).cons
                  (transition t').right⟩

/-- Expand every temporary transition edge back to its two original indexed edges. -/
private def expandTransitions [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {u v : V}
    (p : (M.compressTransitions transition).IndexedWalk u v) : M.IndexedWalk u v :=
  (M.expandTransitionsWithEdges transition p).walk

/-- Map an original edge to the compressed edge that accounts for it. -/
private noncomputable def transitionOwner {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (e : E) :
    M.CompressedTransitionEdge transition :=
  match M.edgePartitionEquiv transition hinj e with
  | Sum.inl f => Sum.inl f
  | Sum.inr p => Sum.inr p.1
end EdgeIndexedMultigraph
end SimpleGraph
namespace SimpleGraph
namespace EdgeIndexedMultigraph

/-- Two distinct indexed edges having the same endpoints. -/
private structure ParallelPair where
  first : E
  second : E
  ne : first ≠ second
  ends_eq : M.ends first = M.ends second

/-- Select one edge identity from a parallel pair. -/
private def ParallelPair.edge {M : EdgeIndexedMultigraph V E}
    (p : M.ParallelPair) : Fin 2 → E :=
  fun i ↦ if i = 0 then p.first else p.second

private theorem ParallelPair.mem_range_edge_iff {M : EdgeIndexedMultigraph V E}
    (p : M.ParallelPair) (e : E) :
    e ∈ Set.range p.edge ↔ e = p.first ∨ e = p.second := by
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i = 0 ∨ i = 1 := by
      have hval : i.val = 0 ∨ i.val = 1 := by omega
      exact hval.imp Fin.ext Fin.ext
    rcases hi with rfl | rfl
    · exact Or.inl (by simp [ParallelPair.edge])
    · exact Or.inr (by simp [ParallelPair.edge])
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [ParallelPair.edge]⟩
    · exact ⟨1, by simp [ParallelPair.edge]⟩

/-- The edge identities left after deleting a parallel pair. -/
private abbrev ErasedParallelPair (p : M.ParallelPair) :=
  {e : E // e ∉ Set.range p.edge}

private instance erasedParallelPairFinite [Finite E] (p : M.ParallelPair) :
    Finite (M.ErasedParallelPair p) :=
  inferInstance

/-- Delete both edge identities in a parallel pair. -/
private def eraseParallelPair (p : M.ParallelPair) :
    EdgeIndexedMultigraph V (M.ErasedParallelPair p) where
  ends e := M.ends e.1
  loopless e := M.loopless e.1

/-- Regard a transition whose edges survive deletion as a transition in the erased multigraph. -/
private def ParallelPair.liftTransition {M : EdgeIndexedMultigraph V E}
    (p : M.ParallelPair) (t : M.EdgeTransition)
    (hleft : t.left ∉ Set.range p.edge) (hright : t.right ∉ Set.range p.edge) :
    (M.eraseParallelPair p).EdgeTransition where
  left := ⟨t.left, hleft⟩
  right := ⟨t.right, hright⟩
  before := t.before
  center := t.center
  after := t.after
  left_ends := t.left_ends
  right_ends := t.right_ends
  before_ne_after := t.before_ne_after

private noncomputable def parallelPairPartition (p : M.ParallelPair) :
    E ≃ M.ErasedParallelPair p ⊕ Fin 2 := by
  classical
  exact
    (Equiv.sumCompl (fun e ↦ e ∈ Set.range p.edge)).symm |>.trans
      (Equiv.sumCongr (Equiv.ofInjective _ p.edge_injective).symm (Equiv.refl _)) |>.trans
      (Equiv.sumComm _ _)
end EdgeIndexedMultigraph
end SimpleGraph
namespace SimpleGraph
namespace Walk

/-- Edge identities in a trail system augmented by arbitrary parity-correcting cycle copies. -/
private abbrev AugmentedTrailEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :=
  c.TrailSystemEdge cover ⊕ c.CycleCopyEdge q

/-- A trail system augmented by arbitrary parity-correcting cycle copies. -/
private noncomputable def augmentedTrailMultigraph (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :
    EdgeIndexedMultigraph V (c.AugmentedTrailEdge cover q) :=
  (c.trailSystemMultigraph cover).disjointSum (c.cycleCopyMultigraph q)

/-- The original cycle edge at an index, viewed in the augmented trail multigraph. -/
private def augmentedOriginalEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (i : Fin c.length) : c.AugmentedTrailEdge cover q :=
  Sum.inl (Sum.inl (ULift.up i))

/-- The unique copied edge at an index whose copy count is one. -/
private def augmentedCopiedEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    {i : Fin c.length} (hi : q.copies i = 1) : c.AugmentedTrailEdge cover q :=
  Sum.inr ⟨i, ⟨0, by omega⟩⟩

/-- A component-cover edge viewed in the augmented trail multigraph. -/
private def augmentedCoverEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (D : c.outsideGraph.ConnectedComponent) (e : (cover D).Edge) :
    c.AugmentedTrailEdge cover q :=
  Sum.inl (Sum.inr ⟨D, e⟩)

/-- An original cycle edge and its parity-correcting copy form a parallel pair. -/
private noncomputable def cycleParallelPair (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    {i : Fin c.length} (hi : q.copies i = 1) :
    (c.augmentedTrailMultigraph cover q).ParallelPair where
  first := c.augmentedOriginalEdge cover q i
  second := c.augmentedCopiedEdge cover q hi
  ne := by simp [augmentedOriginalEdge, augmentedCopiedEdge]
  ends_eq := by
    rw [c.augmentedTrailMultigraph_ends_original,
      c.augmentedTrailMultigraph_ends_copy]

/-- Indices carrying a parity-correcting copy. -/
private abbrev ActiveCycleCopy {n : ℕ} [NeZero n] {d : Fin n → ℕ}
    (q : CyclicParityCompletion d) :=
  {i : Fin n // q.copies i = 1}

/-- The augmented edge identities remaining after one original/copy pair is deleted. -/
private abbrev CutAugmentedTrailEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) :=
  (c.augmentedTrailMultigraph cover q).ErasedParallelPair
    (c.cycleParallelPair cover q cut.2)

/-- Delete the original/copy pair at `cut` from the augmented trail multigraph. -/
private noncomputable def cutAugmentedTrailMultigraph (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) :
    EdgeIndexedMultigraph V (c.CutAugmentedTrailEdge cover q cut) :=
  (c.augmentedTrailMultigraph cover q).eraseParallelPair
    (c.cycleParallelPair cover q cut.2)

/-- Active copied-edge indices other than the deleted index. -/
private abbrev UncutActiveCycleCopy {n : ℕ} [NeZero n] {d : Fin n → ℕ}
    (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q) :=
  {i : ActiveCycleCopy q // i.1 ≠ cut.1}

/-- A retained original edge in the cut augmented multigraph. -/
private noncomputable def cutOriginalEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (j : Fin c.length) (hj : j ≠ cut.1) :
    c.CutAugmentedTrailEdge cover q cut := by
  refine ⟨c.augmentedOriginalEdge cover q j, ?_⟩
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simpa [cycleParallelPair, augmentedOriginalEdge] using hj
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]

/-- A retained copied edge in the cut augmented multigraph. -/
private noncomputable def cutCopiedEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (i : UncutActiveCycleCopy q cut) :
    c.CutAugmentedTrailEdge cover q cut := by
  refine ⟨c.augmentedCopiedEdge cover q i.1.2, ?_⟩
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]
  · intro h
    have hind := congrArg
      (fun e : c.AugmentedTrailEdge cover q ↦ match e with
        | Sum.inl _ => none
        | Sum.inr e => some e.1)
      h
    apply i.2
    exact Option.some.inj
      (by simpa [cycleParallelPair, augmentedCopiedEdge] using hind)

/-- A component-cover edge retained after deleting one cycle-edge pair. -/
private noncomputable def cutCoverEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (D : c.outsideGraph.ConnectedComponent)
    (e : (cover D).Edge) : c.CutAugmentedTrailEdge cover q cut := by
  refine ⟨c.augmentedCoverEdge cover q D e, ?_⟩
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  simp [cycleParallelPair, augmentedCoverEdge, augmentedOriginalEdge,
    augmentedCopiedEdge]

private theorem augmentedCopiedEdge_index_eq (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    {i j : Fin c.length} (hi : q.copies i = 1) (hj : q.copies j = 1)
    (h : c.augmentedCopiedEdge cover q hi = c.augmentedCopiedEdge cover q hj) :
    i = j := by
  have hind := congrArg
    (fun e : c.AugmentedTrailEdge cover q ↦ match e with
      | Sum.inl _ => none
      | Sum.inr e => some e.1)
    h
  exact Option.some.inj (by simpa [augmentedCopiedEdge] using hind)

/-- The final cyclic edge index. -/
private def cycleLastIndex (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, by have := NeZero.pos n; omega⟩

/-- The active copied edge at the final cyclic index. -/
private def lastActiveCycleCopy {n : ℕ} [NeZero n] {d : Fin n → ℕ}
    (q : CyclicParityCompletion d) (hlast : q.copies (cycleLastIndex n) = 1) :
    ActiveCycleCopy q :=
  ⟨cycleLastIndex n, hlast⟩

private theorem fin_val_add_one_lt_of_ne_cycleLastIndex {n : ℕ} [NeZero n]
    (i : Fin n) (hi : i ≠ cycleLastIndex n) : i.val + 1 < n := by
  have hn : 0 < n := NeZero.pos n
  have hilast : i.val ≠ n - 1 := fun h ↦ hi (Fin.ext h)
  omega

/-- Forward forced transitions after deleting the copied closing edge and its original. -/
private noncomputable def forwardLastCutCycleTransition (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) :
    UncutActiveCycleCopy q (lastActiveCycleCopy q hlast) →
      (c.cutAugmentedTrailMultigraph cover q
        (lastActiveCycleCopy q hlast)).EdgeTransition := by
  intro i
  let cut := lastActiveCycleCopy q hlast
  have hi0 := i.1.ne_zero q
  have hiend : i.1.1.val + 1 < c.length := by
    apply fin_val_add_one_lt_of_ne_cycleLastIndex
    simpa [cut, lastActiveCycleCopy] using i.2
  have hpartner : i.1.1 - 1 ≠ cut.1 := by
    intro heq
    have hval := congrArg Fin.val heq
    rw [Fin.val_sub_one_of_ne_zero hi0] at hval
    have hn : 0 < c.length := NeZero.pos c.length
    have hlt := i.1.1.isLt
    change i.1.1.val - 1 = c.length - 1 at hval
    omega
  have hleft :
      (c.cutAugmentedTrailMultigraph cover q cut).ends
          (c.cutOriginalEdge cover q cut (i.1.1 - 1) hpartner) =
        s(c.getVert (i.1.1.val - 1), c.getVert i.1.1.val) := by
    rw [c.cutAugmentedTrailMultigraph_ends_original]
    rw [Fin.val_sub_one_of_ne_zero hi0]
    have hpos : 0 < i.1.1.val :=
      Nat.pos_of_ne_zero (fun h ↦ hi0 (Fin.ext h))
    rw [Nat.sub_add_cancel hpos]
  have hright :
      (c.cutAugmentedTrailMultigraph cover q cut).ends
          (c.cutCopiedEdge cover q cut i) =
        s(c.getVert i.1.1, c.getVert (i.1.1.val + 1)) :=
    c.cutAugmentedTrailMultigraph_ends_copy cover q cut i
  exact {
    left := c.cutOriginalEdge cover q cut (i.1.1 - 1) hpartner
    right := c.cutCopiedEdge cover q cut i
    before := c.getVert (i.1.1.val - 1)
    center := c.getVert i.1.1.val
    after := c.getVert (i.1.1.val + 1)
    left_ends := hleft
    right_ends := hright
    before_ne_after :=
      hc.getVert_sub_one_ne_getVert_add_one (Nat.le_of_lt i.1.1.isLt) }

/-- The forward closing-edge-cut transitions are pairwise edge-disjoint. -/
private theorem forwardLastCutCycleTransition_edge_injective (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) :
    Function.Injective
      ((c.cutAugmentedTrailMultigraph cover q (lastActiveCycleCopy q hlast)).transitionEdge
        (c.forwardLastCutCycleTransition hc cover q hlast)) := by
  intro a b hab
  rcases a with ⟨i, side⟩
  rcases b with ⟨j, side'⟩
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have hside' : side' = 0 ∨ side' = 1 := by
    have hval : side'.val = 0 ∨ side'.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hside with rfl | rfl <;> rcases hside' with rfl | rfl
  · have hval := congrArg Subtype.val hab
    have hind : i.1.1 - 1 = j.1.1 - 1 := by
      simpa [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
        cutOriginalEdge, augmentedOriginalEdge] using hval
    have hij : i = j := by
      apply Subtype.ext
      apply Subtype.ext
      exact sub_left_injective hind
    subst j
    rfl
  · have hval := congrArg Subtype.val hab
    simp [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
      cutOriginalEdge, cutCopiedEdge, augmentedOriginalEdge, augmentedCopiedEdge] at hval
  · have hval := congrArg Subtype.val hab
    simp [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
      cutOriginalEdge, cutCopiedEdge, augmentedOriginalEdge, augmentedCopiedEdge] at hval
  · have hval := congrArg Subtype.val hab
    have hind : i.1.1 = j.1.1 := by
      apply augmentedCopiedEdge_index_eq c cover q i.1.2 j.1.2
      simpa [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
        cutCopiedEdge] using hval
    have hij : i = j := by
      apply Subtype.ext
      exact Subtype.ext hind
    subst j
    rfl

/-- The original edge paired with a copied edge on the two root-to-`k` arcs. -/
private def splitPartnerIndex {n : ℕ} [NeZero n] (k : Fin n) (i : Fin n) : Fin n :=
  if i.val < k.val then i - 1 else i + 1

private theorem splitPartnerIndex_val_on_active {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) (i : ActiveCycleCopy q) :
    (splitPartnerIndex k i.1).val =
      if i.1.val < k.val then i.1.val - 1 else i.1.val + 1 := by
  by_cases h : i.1.val < k.val
  · rw [splitPartnerIndex, ite_eq_left h, ite_eq_left h,
      Fin.val_sub_one_of_ne_zero (i.ne_zero q)]
  · have hiend := i.val_add_one_lt q hlast
    have hn2 : 1 < n :=
      lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le i.1.val)) hiend
    have hone : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt hn2
    have hadd : i.1.val + (1 : Fin n).val < n := by
      rw [hone]
      exact hiend
    rw [splitPartnerIndex, ite_eq_right h, ite_eq_right h]
    exact (Fin.val_add_eq_of_add_lt hadd).trans (by rw [hone])

private theorem splitPartnerIndex_injective_on_active {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) :
    Function.Injective
      (fun i : ActiveCycleCopy q ↦ splitPartnerIndex k i.1) := by
  intro i j hij
  have hipos : 0 < i.1.val := by
    have hi0 := i.ne_zero q
    exact Nat.pos_of_ne_zero (fun h ↦ hi0 (Fin.ext h))
  have hjpos : 0 < j.1.val := by
    have hj0 := j.ne_zero q
    exact Nat.pos_of_ne_zero (fun h ↦ hj0 (Fin.ext h))
  apply Subtype.ext
  apply Fin.ext
  have hval := congrArg Fin.val hij
  change (splitPartnerIndex k i.1).val = (splitPartnerIndex k j.1).val at hval
  have hvali := splitPartnerIndex_val_on_active q k hlast i
  have hvalj := splitPartnerIndex_val_on_active q k hlast j
  have heq : (if i.1.val < k.val then i.1.val - 1 else i.1.val + 1) =
      if j.1.val < k.val then j.1.val - 1 else j.1.val + 1 :=
    hvali.symm.trans (hval.trans hvalj)
  by_cases hiklt : i.1.val < k.val <;> by_cases hjklt : j.1.val < k.val
  · simp [hiklt, hjklt] at heq
    omega
  · simp [hiklt, hjklt] at heq
    omega
  · simp [hiklt, hjklt] at heq
    omega
  · simp [hiklt, hjklt] at heq
    omega

/-- The forced transition associated to every copied edge when neither terminal arc edge is
copied. -/
private noncomputable def splitCycleTransition (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    ActiveCycleCopy q → (c.augmentedTrailMultigraph cover q).EdgeTransition := by
  intro i
  let partner := splitPartnerIndex k i.1
  by_cases hforward : i.1.val < k.val
  · have hi0 := i.ne_zero q
    have hpartner : partner = i.1 - 1 := by simp [partner, splitPartnerIndex, hforward]
    have hleft :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedOriginalEdge cover q partner) =
          s(c.getVert (i.1.val - 1), c.getVert i.1.val) := by
      rw [hpartner, c.augmentedTrailMultigraph_ends_original]
      rw [Fin.val_sub_one_of_ne_zero hi0]
      have hpos : 0 < i.1.val := Nat.pos_of_ne_zero (by
        intro h
        apply hi0
        apply Fin.ext
        exact h)
      rw [Nat.sub_add_cancel hpos]
    have hright :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedCopiedEdge cover q i.2) =
          s(c.getVert i.1, c.getVert (i.1.val + 1)) :=
      c.augmentedTrailMultigraph_ends_copy cover q i.2
    exact {
      left := c.augmentedOriginalEdge cover q partner
      right := c.augmentedCopiedEdge cover q i.2
      before := c.getVert (i.1.val - 1)
      center := c.getVert i.1.val
      after := c.getVert (i.1.val + 1)
      left_ends := hleft
      right_ends := hright
      before_ne_after := by
        exact hc.getVert_sub_one_ne_getVert_add_one (Nat.le_of_lt i.1.isLt) }
  · have hiend := i.val_add_one_lt q hlast
    have hn2 : 1 < c.length :=
      lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le i.1.val)) hiend
    have hone : (1 : Fin c.length).val = 1 := Nat.mod_eq_of_lt hn2
    have hadd : i.1.val + (1 : Fin c.length).val < c.length := by
      rw [hone]
      exact hiend
    have hpartner : partner = i.1 + 1 := by simp [partner, splitPartnerIndex, hforward]
    have hleft :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedOriginalEdge cover q partner) =
          s(c.getVert (i.1.val + 2), c.getVert (i.1.val + 1)) := by
      rw [hpartner, c.augmentedTrailMultigraph_ends_original,
        Fin.val_add_eq_of_add_lt hadd, hone]
      exact Sym2.eq_swap
    have hright :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedCopiedEdge cover q i.2) =
          s(c.getVert (i.1.val + 1), c.getVert i.1.val) := by
      rw [c.augmentedTrailMultigraph_ends_copy, Sym2.eq_swap]
    exact {
      left := c.augmentedOriginalEdge cover q partner
      right := c.augmentedCopiedEdge cover q i.2
      before := c.getVert (i.1.val + 2)
      center := c.getVert (i.1.val + 1)
      after := c.getVert i.1.val
      left_ends := hleft
      right_ends := hright
      before_ne_after := by
        have hne := hc.getVert_sub_one_ne_getVert_add_one
          (i := i.1.val + 1) (by omega : i.1.val + 1 ≤ c.length)
        simpa using hne.symm }

private theorem splitPartnerIndex_ne_cut {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q)
    (hlast : q.copies (cycleLastIndex n) = 0)
    (i : UncutActiveCycleCopy q cut) :
    splitPartnerIndex cut.1 i.1.1 ≠ cut.1 := by
  intro h
  have hval := congrArg Fin.val h
  rw [splitPartnerIndex_val_on_active q cut.1 hlast i.1] at hval
  have hipos : 0 < i.1.1.val :=
    Nat.pos_of_ne_zero (fun hzero ↦ i.1.ne_zero q (Fin.ext hzero))
  by_cases hlt : i.1.1.val < cut.1.val
  · simp [hlt] at hval
    omega
  · simp [hlt] at hval
    have hneval : i.1.1.val ≠ cut.1.val := fun heq ↦ i.2 (Fin.ext heq)
    omega

private theorem splitCycleTransition_left_survives_cut (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) :
    (c.splitCycleTransition hc cover q cut.1 hlast i.1).left ∉
      Set.range (c.cycleParallelPair cover q cut.2).edge := by
  rw [c.splitCycleTransition_left]
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simpa [cycleParallelPair, augmentedOriginalEdge] using
      splitPartnerIndex_ne_cut q cut hlast i
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]

private theorem splitCycleTransition_right_survives_cut (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) :
    (c.splitCycleTransition hc cover q cut.1 hlast i.1).right ∉
      Set.range (c.cycleParallelPair cover q cut.2).edge := by
  rw [c.splitCycleTransition_right]
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]
  · intro h
    exact i.2 (augmentedCopiedEdge_index_eq c cover q i.1.2 cut.2 h)

/-- Forced transitions after deleting the original/copy pair at the arc endpoint `cut`. -/
private noncomputable def cutSplitCycleTransition (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    UncutActiveCycleCopy q cut →
      (c.cutAugmentedTrailMultigraph cover q cut).EdgeTransition :=
  fun i ↦ (c.cycleParallelPair cover q cut.2).liftTransition
    (c.splitCycleTransition hc cover q cut.1 hlast i.1)
    (splitCycleTransition_left_survives_cut c hc cover q cut hlast i)
    (splitCycleTransition_right_survives_cut c hc cover q cut hlast i)

/-- The paired original/copy edge identities are all distinct. -/
private theorem splitCycleTransition_edge_injective (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    Function.Injective ((c.augmentedTrailMultigraph cover q).transitionEdge
      (c.splitCycleTransition hc cover q k hlast)) := by
  intro a b hab
  rcases a with ⟨i, side⟩
  rcases b with ⟨j, side'⟩
  have hpartner := splitPartnerIndex_injective_on_active q k hlast
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have hside' : side' = 0 ∨ side' = 1 := by
    have hval : side'.val = 0 ∨ side'.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hside with rfl | rfl <;> rcases hside' with rfl | rfl
  · have hij : splitPartnerIndex k i.1 = splitPartnerIndex k j.1 := by
      simpa [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge] using hab
    have hij' : i = j := hpartner hij
    subst j
    rfl
  · simp [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge,
      augmentedCopiedEdge] at hab
  · simp [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge,
      augmentedCopiedEdge] at hab
  · have hij : i.1 = j.1 := by
      simp only [EdgeIndexedMultigraph.transitionEdge, Fin.isValue, one_ne_zero,
        ↓reduceIte, splitCycleTransition_right, augmentedCopiedEdge,
        Sum.inr.injEq, Sigma.mk.injEq] at hab
      exact hab.1
    apply Prod.ext
    · exact Subtype.ext hij
    · rfl

end Walk
end SimpleGraph
namespace SimpleGraph
end SimpleGraph
namespace SimpleGraph
namespace Walk
/-- The augmented trail multigraph after the two-arc transitions are compressed. -/
private noncomputable def splitCompressedMultigraph (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :=
  (c.augmentedTrailMultigraph cover q).compressTransitions
    (c.splitCycleTransition hc cover q k hlast)

/-- The closing-edge-cut multigraph after its forward transitions are compressed. -/
private noncomputable def forwardLastCutCompressedMultigraph (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) :=
  (c.cutAugmentedTrailMultigraph cover q (lastActiveCycleCopy q hlast)).compressTransitions
    (c.forwardLastCutCycleTransition hc cover q hlast)

/-- The distinguished-edge-cut multigraph after its two-arc transitions are compressed. -/
private noncomputable def cutSplitCompressedMultigraph (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0) :=
  (c.cutAugmentedTrailMultigraph cover q cut).compressTransitions
    (c.cutSplitCycleTransition hc cover q cut hlast)

private theorem split_partner_ne_forward_original {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k j : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) (hjk : j.val < k.val)
    (hzero : ∀ h : j.val + 1 < k.val,
      q.copies ⟨j.val + 1, lt_trans h k.isLt⟩ = 0)
    (i : ActiveCycleCopy q) : splitPartnerIndex k i.1 ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [splitPartnerIndex_val_on_active q k hlast i] at hval
  have hipos : 0 < i.1.val :=
    Nat.pos_of_ne_zero (fun h ↦ i.ne_zero q (Fin.ext h))
  by_cases hik : i.1.val < k.val
  · simp [hik] at hval
    have hjnext : j.val + 1 < k.val := by omega
    have hinext : i.1 = ⟨j.val + 1, lt_trans hjnext k.isLt⟩ := by
      apply Fin.ext
      change i.1.val = j.val + 1
      omega
    have hone := i.2
    rw [hinext, hzero hjnext] at hone
    omega
  · simp [hik] at hval
    omega

private theorem split_partner_ne_reverse_original {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k j : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) (hkj : k.val ≤ j.val)
    (hzero : k.val < j.val →
      q.copies ⟨j.val - 1, by omega⟩ = 0)
    (i : ActiveCycleCopy q) : splitPartnerIndex k i.1 ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [splitPartnerIndex_val_on_active q k hlast i] at hval
  have hipos : 0 < i.1.val :=
    Nat.pos_of_ne_zero (fun h ↦ i.ne_zero q (Fin.ext h))
  by_cases hik : i.1.val < k.val
  · simp [hik] at hval
    omega
  · simp [hik] at hval
    have hiend := i.val_add_one_lt q hlast
    by_cases hkj' : k.val = j.val
    · omega
    · have hkjlt : k.val < j.val := by omega
      have hiprev : i.1 = ⟨j.val - 1, by omega⟩ := by
        apply Fin.ext
        change i.1.val = j.val - 1
        omega
      have hone := i.2
      rw [hiprev, hzero hkjlt] at hone
      omega

private theorem split_forward_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hr : r ≤ k.val) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Reachable
      (c.getVert r) x := by
  let selected : ℕ → Prop := fun t ↦
    ∃ ht : t < c.length, t < k.val ∧ q.copies ⟨t, ht⟩ = 1
  have hterminal : ¬selected k.val := by
    rintro ⟨hklen, hkk, hcopy⟩
    omega
  have hadj : ∀ i, i < k.val → ¬selected (i + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 1)) := by
    intro i hik hnsel
    let j : Fin c.length := ⟨i, lt_trans hik k.isLt⟩
    apply c.split_compressed_adj_original hc cover q k hlast j
    apply split_partner_ne_forward_original q k j hlast
    · exact hik
    · intro hinext
      have hcopy : q.copies
          ⟨j.val + 1, lt_trans hinext k.isLt⟩ = 0 := by
        by_contra hzero
        have hone : q.copies ⟨j.val + 1, lt_trans hinext k.isLt⟩ = 1 := by
          have hlt := q.copies_lt_two ⟨j.val + 1, lt_trans hinext k.isLt⟩
          omega
        apply hnsel
        exact ⟨lt_trans hinext k.isLt, hinext, hone⟩
      exact hcopy
  have hskip : ∀ i, i + 2 ≤ k.val → selected (i + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 2)) := by
    rintro i hi2 ⟨hi1len, hi1k, hcopy⟩
    let a : ActiveCycleCopy q := ⟨⟨i + 1, hi1len⟩, hcopy⟩
    have h := c.split_compressed_adj_forward_skip hc cover q k hlast a hi1k
    simpa [a] using h
  have hpath := reachable_of_adj_or_skip
    (G := (c.splitCompressedMultigraph hc cover q k hlast).underlying)
    (fun i ↦ c.getVert i) k.val selected hterminal hadj hskip
  have hroot := hpath 0 (Nat.zero_le k.val)
  exact (hpath r hr).trans (by simpa using hroot.symm)

private theorem split_reverse_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hkr : k.val ≤ r) (hrn : r < c.length) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Reachable
      (c.getVert r) x := by
  let m := c.length - k.val
  let selected : ℕ → Prop := fun t ↦
    ∃ i : ActiveCycleCopy q, ¬i.1.val < k.val ∧ i.1.val + t + 1 = c.length
  have hterminal : ¬selected m := by
    rintro ⟨i, hik, hi⟩
    dsimp [m] at hi
    omega
  have hadj : ∀ a, a < m → ¬selected (a + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 1))) := by
    intro a ham hnsel
    let j : Fin c.length := ⟨c.length - a - 1, by
      have hn := NeZero.pos c.length
      dsimp [m] at ham
      omega⟩
    have hkj : k.val ≤ j.val := by
      dsimp [j, m] at ham ⊢
      omega
    have hnotpaired : ∀ i : ActiveCycleCopy q, splitPartnerIndex k i.1 ≠ j := by
      apply split_partner_ne_reverse_original q k j hlast hkj
      intro hkjlt
      by_contra hzero
      have hone : q.copies ⟨j.val - 1, by omega⟩ = 1 := by
        have hlt := q.copies_lt_two ⟨j.val - 1, by omega⟩
        omega
      let i : ActiveCycleCopy q := ⟨⟨j.val - 1, by omega⟩, hone⟩
      apply hnsel
      refine ⟨i, ?_, ?_⟩
      · dsimp [i]
        omega
      · change (j.val - 1) + (a + 1) + 1 = c.length
        have hjval : j.val = c.length - a - 1 := rfl
        omega
    have horig := c.split_compressed_adj_original hc cover q k hlast j hnotpaired
    have hsucc : c.getVert (j + 1) = c.getVert (c.length - a) := by
      congr 1
      dsimp [j, m] at ham ⊢
      omega
    rw [hsucc] at horig
    exact horig.symm
  have hskip : ∀ a, a + 2 ≤ m → selected (a + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 2))) := by
    rintro a ha2 ⟨i, hik, hi⟩
    have h := c.split_compressed_adj_reverse_skip hc cover q k hlast i hik
    dsimp [m] at ha2
    convert h using 1 <;> congr 1 <;> omega
  have hpath := reachable_of_adj_or_skip
    (G := (c.splitCompressedMultigraph hc cover q k hlast).underlying)
    (fun t ↦ c.getVert (c.length - t)) m selected hterminal hadj hskip
  have ht : c.length - r ≤ m := by
    dsimp [m]
    omega
  have hroot := hpath 0 (Nat.zero_le m)
  have hrpath := hpath (c.length - r) ht
  simpa [m, Nat.sub_sub_self (Nat.le_of_lt hrn)] using hrpath.trans hroot.symm

private noncomputable def splitCompressedCoverHom (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (D : c.outsideGraph.ConnectedComponent) :
    (cover D).multigraph.underlying →g
      (c.splitCompressedMultigraph hc cover q k hlast).underlying where
  toFun := id
  map_rel' := by
    intro u v huv
    obtain ⟨e, he⟩ := (cover D).multigraph.underlying_adj.mp huv
    apply (c.splitCompressedMultigraph hc cover q k hlast).underlying_adj.mpr
    refine ⟨Sum.inl ⟨c.augmentedCoverEdge cover q D e, ?_⟩, ?_⟩
    · rintro ⟨⟨i, side⟩, hi⟩
      have hside : side = 0 ∨ side = 1 := by
        have hval : side.val = 0 ∨ side.val = 1 := by omega
        exact hval.imp Fin.ext Fin.ext
      rcases hside with rfl | rfl
      · simp [EdgeIndexedMultigraph.transitionEdge, augmentedCoverEdge,
          augmentedOriginalEdge] at hi
      · simp [EdgeIndexedMultigraph.transitionEdge, augmentedCoverEdge,
          augmentedCopiedEdge] at hi
    · exact (c.augmentedTrailMultigraph_ends_cover cover q D e).trans he

private noncomputable def forwardLastCompressedCoverHom (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1)
    (D : c.outsideGraph.ConnectedComponent) :
    (cover D).multigraph.underlying →g
      (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying where
  toFun := id
  map_rel' := by
    intro u v huv
    obtain ⟨e, he⟩ := (cover D).multigraph.underlying_adj.mp huv
    let cut := lastActiveCycleCopy q hlast
    let edge := c.cutCoverEdge cover q cut D e
    apply (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying_adj.mpr
    refine ⟨Sum.inl ⟨edge, ?_⟩, ?_⟩
    · rintro ⟨⟨i, side⟩, hi⟩
      have hval := congrArg Subtype.val hi
      have hside : side = 0 ∨ side = 1 := by
        have hsval : side.val = 0 ∨ side.val = 1 := by omega
        exact hsval.imp Fin.ext Fin.ext
      rcases hside with rfl | rfl
      · have hcycle : c.augmentedCoverEdge cover q D e =
            c.augmentedOriginalEdge cover q (i.1.1 - 1) := by
          simpa [edge, EdgeIndexedMultigraph.transitionEdge,
            forwardLastCutCycleTransition, cutCoverEdge, cutOriginalEdge] using hval.symm
        simp [augmentedCoverEdge, augmentedOriginalEdge] at hcycle
      · have hcycle : c.augmentedCoverEdge cover q D e =
            c.augmentedCopiedEdge cover q i.1.2 := by
          simpa [edge, EdgeIndexedMultigraph.transitionEdge,
            forwardLastCutCycleTransition, cutCoverEdge, cutCopiedEdge] using hval.symm
        simp [augmentedCoverEdge, augmentedCopiedEdge] at hcycle
    · exact (c.cutAugmentedTrailMultigraph_ends_cover cover q cut D e).trans he

private theorem cutSplit_forward_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hr : r ≤ cut.1.val) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Reachable
      (c.getVert r) x := by
  let selected : ℕ → Prop := fun t ↦
    ∃ ht : t < c.length, t < cut.1.val ∧ q.copies ⟨t, ht⟩ = 1
  have hterminal : ¬selected cut.1.val := by
    rintro ⟨hlen, hlt, hcopy⟩
    omega
  have hadj : ∀ i, i < cut.1.val → ¬selected (i + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 1)) := by
    intro i hicut hnsel
    let j : Fin c.length := ⟨i, lt_trans hicut cut.1.isLt⟩
    have hjcut : j ≠ cut.1 := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [j] at hval
      omega
    apply c.cutSplit_compressed_adj_original hc cover q cut hlast j hjcut
    intro a
    apply split_partner_ne_forward_original q cut.1 j hlast hicut
    intro hinext
    by_contra hzero
    have hone : q.copies ⟨j.val + 1, lt_trans hinext cut.1.isLt⟩ = 1 := by
      have hlt := q.copies_lt_two ⟨j.val + 1, lt_trans hinext cut.1.isLt⟩
      omega
    apply hnsel
    exact ⟨lt_trans hinext cut.1.isLt, hinext, hone⟩
  have hskip : ∀ i, i + 2 ≤ cut.1.val → selected (i + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 2)) := by
    rintro i hi2 ⟨hi1len, hi1cut, hcopy⟩
    let a : ActiveCycleCopy q := ⟨⟨i + 1, hi1len⟩, hcopy⟩
    have hane : a.1 ≠ cut.1 := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [a] at hval
      omega
    let a' : UncutActiveCycleCopy q cut := ⟨a, hane⟩
    have h := c.cutSplit_compressed_adj_forward_skip hc cover q cut hlast a' hi1cut
    change (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
      (c.getVert ((i + 1) - 1)) (c.getVert ((i + 1) + 1)) at h
    convert h using 1
    all_goals congr 1
  have hpath := reachable_of_adj_or_skip
    (G := (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying)
    (fun i ↦ c.getVert i) cut.1.val selected hterminal hadj hskip
  have hroot := hpath 0 (Nat.zero_le cut.1.val)
  exact (hpath r hr).trans (by simpa using hroot.symm)

private theorem cut_split_partner_ne_reverse_original {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q)
    (j : Fin n) (hlast : q.copies (cycleLastIndex n) = 0)
    (hcutj : cut.1.val < j.val)
    (hzero : cut.1.val + 1 < j.val → q.copies ⟨j.val - 1, by omega⟩ = 0)
    (i : UncutActiveCycleCopy q cut) :
    splitPartnerIndex cut.1 i.1.1 ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [splitPartnerIndex_val_on_active q cut.1 hlast i.1] at hval
  have hipos : 0 < i.1.1.val :=
    Nat.pos_of_ne_zero (fun h ↦ i.1.ne_zero q (Fin.ext h))
  by_cases hik : i.1.1.val < cut.1.val
  · simp [hik] at hval
    omega
  · simp [hik] at hval
    by_cases hjnext : j.val = cut.1.val + 1
    · apply i.2
      apply Fin.ext
      omega
    · have hcutj' : cut.1.val + 1 < j.val := by omega
      have hiprev : i.1.1 = ⟨j.val - 1, by omega⟩ := by
        apply Fin.ext
        change i.1.1.val = j.val - 1
        omega
      have hone := i.1.2
      rw [hiprev, hzero hcutj'] at hone
      omega

private theorem cutSplit_reverse_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hcutr : cut.1.val + 1 ≤ r) (hrn : r < c.length) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Reachable
      (c.getVert r) x := by
  let m := c.length - (cut.1.val + 1)
  let selected : ℕ → Prop := fun t ↦
    ∃ i : UncutActiveCycleCopy q cut,
      ¬i.1.1.val < cut.1.val ∧ i.1.1.val + t + 1 = c.length
  have hterminal : ¬selected m := by
    rintro ⟨i, hik, hi⟩
    have hval : i.1.1.val = cut.1.val := by
      dsimp [m] at hi
      omega
    exact i.2 (Fin.ext hval)
  have hadj : ∀ a, a < m → ¬selected (a + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 1))) := by
    intro a ham hnsel
    let j : Fin c.length := ⟨c.length - a - 1, by
      have hn := NeZero.pos c.length
      dsimp [m] at ham
      omega⟩
    have hcutj : cut.1.val < j.val := by
      dsimp [j, m] at ham ⊢
      omega
    have hjcut : j ≠ cut.1 := fun h ↦ by
      have hval := congrArg Fin.val h
      omega
    have hnotpaired : ∀ i : UncutActiveCycleCopy q cut,
        splitPartnerIndex cut.1 i.1.1 ≠ j := by
      intro i
      apply cut_split_partner_ne_reverse_original q cut j hlast hcutj
      intro hcutj'
      by_contra hzero
      have hone : q.copies ⟨j.val - 1, by omega⟩ = 1 := by
        have hlt := q.copies_lt_two ⟨j.val - 1, by omega⟩
        omega
      let i' : ActiveCycleCopy q := ⟨⟨j.val - 1, by omega⟩, hone⟩
      have hine : i'.1 ≠ cut.1 := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp [i'] at hval
        omega
      apply hnsel
      refine ⟨⟨i', hine⟩, ?_, ?_⟩
      · dsimp [i']
        omega
      · change (j.val - 1) + (a + 1) + 1 = c.length
        have hjval : j.val = c.length - a - 1 := rfl
        omega
    have horig :=
      c.cutSplit_compressed_adj_original hc cover q cut hlast j hjcut hnotpaired
    have hsucc : c.getVert (j + 1) = c.getVert (c.length - a) := by
      congr 1
      dsimp [j, m] at ham ⊢
      omega
    rw [hsucc] at horig
    exact horig.symm
  have hskip : ∀ a, a + 2 ≤ m → selected (a + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 2))) := by
    rintro a ha2 ⟨i, hik, hi⟩
    have h := c.cutSplit_compressed_adj_reverse_skip hc cover q cut hlast i hik
    dsimp [m] at ha2
    convert h using 1 <;> congr 1 <;> omega
  have hpath := reachable_of_adj_or_skip
    (G := (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying)
    (fun t ↦ c.getVert (c.length - t)) m selected hterminal hadj hskip
  have ht : c.length - r ≤ m := by
    dsimp [m]
    omega
  have hroot := hpath 0 (Nat.zero_le m)
  have hrpath := hpath (c.length - r) ht
  simpa [m, Nat.sub_sub_self (Nat.le_of_lt hrn)] using hrpath.trans hroot.symm

private noncomputable def cutSplitCompressedCoverHom (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (D : c.outsideGraph.ConnectedComponent) :
    (cover D).multigraph.underlying →g
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying where
  toFun := id
  map_rel' := by
    intro u v huv
    obtain ⟨e, he⟩ := (cover D).multigraph.underlying_adj.mp huv
    let edge := c.cutCoverEdge cover q cut D e
    apply (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying_adj.mpr
    refine ⟨Sum.inl ⟨edge, ?_⟩, ?_⟩
    · rintro ⟨⟨i, side⟩, hi⟩
      have hval := congrArg Subtype.val hi
      have hside : side = 0 ∨ side = 1 := by
        have hsval : side.val = 0 ∨ side.val = 1 := by omega
        exact hsval.imp Fin.ext Fin.ext
      rcases hside with rfl | rfl
      · have hcycle : c.augmentedCoverEdge cover q D e =
            c.augmentedOriginalEdge cover q (splitPartnerIndex cut.1 i.1.1) := by
          simpa [edge, EdgeIndexedMultigraph.transitionEdge,
            cutSplitCycleTransition, EdgeIndexedMultigraph.ParallelPair.liftTransition,
            cutCoverEdge, cutOriginalEdge] using hval.symm
        simp [augmentedCoverEdge, augmentedOriginalEdge] at hcycle
      · have hcycle : c.augmentedCoverEdge cover q D e =
            c.augmentedCopiedEdge cover q i.1.2 := by
          simpa [edge, EdgeIndexedMultigraph.transitionEdge,
            cutSplitCycleTransition, EdgeIndexedMultigraph.ParallelPair.liftTransition,
            cutCoverEdge, cutCopiedEdge] using hval.symm
        simp [augmentedCoverEdge, augmentedCopiedEdge] at hcycle
    · exact (c.cutAugmentedTrailMultigraph_ends_cover cover q cut D e).trans he

end Walk
end SimpleGraph
namespace SimpleGraph
namespace Walk
end Walk
end SimpleGraph
namespace SimpleGraph
namespace EdgeIndexedMultigraph
/-- The next position in a nonempty finite cyclic order. -/
private def cyclicNext (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- The previous position in a nonempty finite cyclic order. -/
private def cyclicPrev (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩

/-- A finite directed traversal of every edge identity around one circuit. -/
private structure CyclicCircuit where
  /-- Number of edge positions. -/
  size : ℕ
  size_pos : 0 < size
  /-- Vertex before the edge at a cyclic position. -/
  vertex : Fin size → V
  /-- Edge traversed from this position to the next one. -/
  edge : Fin size → E
  /-- The indexed edge has the displayed consecutive endpoints. -/
  ends_edge : ∀ i, M.ends (edge i) =
    s(vertex i, vertex (cyclicNext size size_pos i))
  /-- Every edge identity occurs exactly once. -/
  edge_bijective : Function.Bijective edge

namespace IndexedWalk

private theorem getVert_succ_fin {x : V} (p : M.IndexedWalk x x) (hne : p.edges ≠ [])
    (i : Fin p.edges.length) :
    p.toWalk.getVert (i.val + 1) =
      p.toWalk.getVert (cyclicNext p.edges.length (List.length_pos_of_ne_nil hne) i).val := by
  by_cases hlt : i.val + 1 < p.edges.length
  · simp [cyclicNext, Nat.mod_eq_of_lt hlt]
  · have heq : i.val + 1 = p.edges.length := by omega
    have hlength : p.toWalk.length = p.edges.length := p.length_toWalk
    calc
      p.toWalk.getVert (i.val + 1) = x := by
        rw [heq, ← hlength, p.toWalk.getVert_length]
      _ = p.toWalk.getVert 0 := p.toWalk.getVert_zero.symm
      _ = p.toWalk.getVert
          (cyclicNext p.edges.length (List.length_pos_of_ne_nil hne) i).val := by
        congr 1
        simp [cyclicNext, heq]

/-- An indexed Euler circuit with at least one edge gives a cyclic edge-position encoding. -/
private noncomputable def toCyclicCircuit [Nonempty E] {x : V}
    (p : M.IndexedWalk x x) (hp : p.IsEulerian) : M.CyclicCircuit := by
  classical
  have hne : p.edges ≠ [] := by
    let e : E := Classical.choice (inferInstance : Nonempty E)
    exact fun h ↦ by simpa [h] using hp.2 e
  refine {
    size := p.edges.length
    size_pos := List.length_pos_of_ne_nil hne
    vertex := fun i ↦ p.toWalk.getVert i.val
    edge := p.edges.get
    ends_edge := ?_
    edge_bijective := ?_ }
  · intro i
    have hi : i.val < p.toWalk.edges.length := by
      rw [p.toWalk.length_edges, p.length_toWalk]
      exact i.isLt
    have hedge := p.toWalk.getElem_edges hi
    have hmap : p.toWalk.edges[i.val]'hi = M.ends (p.edges[i.val]'i.isLt) := by
      simp only [p.edges_toWalk, List.getElem_map]
    calc
      M.ends (p.edges.get i) = p.toWalk.edges.get ⟨i.val, hi⟩ := hmap.symm
      _ = s(p.toWalk.getVert i.val, p.toWalk.getVert (i.val + 1)) := by
        simpa using hedge
      _ = s(p.toWalk.getVert i.val,
          p.toWalk.getVert
            (cyclicNext p.edges.length (List.length_pos_of_ne_nil hne) i).val) :=
        congrArg (s(p.toWalk.getVert i.val, ·)) (getVert_succ_fin M p hne i)
  · constructor
    · exact hp.1.injective_get
    · intro e
      exact List.mem_iff_get.mp (hp.2 e)

end IndexedWalk

namespace CyclicCircuit

variable (C : M.CyclicCircuit)

/-- Add an offset to a cyclic position, using the circuit size as modulus. -/
private def rotatedPosition (start i : Fin C.size) : Fin C.size :=
  let _ : NeZero C.size := ⟨Nat.ne_of_gt C.size_pos⟩
  start + i

/-- All cyclic positions, starting at a prescribed position. -/
private def rotatedPositions (start : Fin C.size) : List (Fin C.size) :=
  List.ofFn fun i ↦ C.rotatedPosition M start i

/-- A cyclic position list with the initial position repeated at the end. -/
private def closedRotatedPosition (start : Fin C.size) (i : Fin (C.size + 1)) :
    Fin C.size :=
  if hi : i.val < C.size then C.rotatedPosition M start ⟨i.val, hi⟩ else start

/-- Vertices and pass marks in cyclic order, with the initial entry repeated at the end. -/
private def markedVertexListing (start : Fin C.size) (marked : Fin C.size → Bool) :
    List (V × Bool) :=
  List.ofFn fun i ↦
    let j := C.closedRotatedPosition M start i
    (C.vertex j, marked j)

/-- Keep an unmarked cyclic occurrence and discard a marked occurrence. -/
private def keptVertex (marked : Fin C.size → Bool) (i : Fin C.size) : Option V :=
  if marked i then none else some (C.vertex i)

/-- The unmarked vertices in one nonrepeating turn around the circuit. -/
private def keptCoreVertices (start : Fin C.size) (marked : Fin C.size → Bool) :
    List V :=
  (C.rotatedPositions M start).filterMap (C.keptVertex M marked)

/-- The unmarked cyclic listing, closed by repeating its initial vertex. -/
private def keptVertexListing (start : Fin C.size) (marked : Fin C.size → Bool) :
    List V :=
  C.keptCoreVertices M start marked ++ [C.vertex start]

private theorem rotatedPositions_eq_cons_cons (start : Fin C.size)
    (hsize : 2 ≤ C.size) :
    ∃ l, C.rotatedPositions M start =
      start :: cyclicNext C.size C.size_pos start :: l := by
  have hlength : (C.rotatedPositions M start).length = C.size := by
    simp [rotatedPositions]
  have hget0 : (C.rotatedPositions M start)[0]? = some start := by
    change (List.ofFn fun i ↦ C.rotatedPosition M start i)[0]? = some start
    rw [List.getElem?_ofFn]
    simp only [dite_eq_left C.size_pos]
    congr 1
    apply Fin.ext
    simp [rotatedPosition, Fin.val_add, Nat.mod_eq_of_lt start.isLt]
  have hget1 : (C.rotatedPositions M start)[1]? =
      some (cyclicNext C.size C.size_pos start) := by
    change (List.ofFn fun i ↦ C.rotatedPosition M start i)[1]? = _
    rw [List.getElem?_ofFn]
    split
    · rename_i hone
      congr 1
    · omega
  cases hrot : C.rotatedPositions M start with
  | nil =>
      exfalso
      rw [hrot] at hlength
      simp at hlength
      omega
  | cons a l =>
      cases hl : l with
      | nil =>
          exfalso
          rw [hrot, hl] at hlength
          simp at hlength
          omega
      | cons b t =>
          rw [hrot, hl] at hget0 hget1
          have ha : a = start := by
            simpa only [List.getElem?_cons_zero, Option.some.injEq] using hget0
          have hb : b = cyclicNext C.size C.size_pos start := by
            simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] using hget1
          rw [ha, hb]
          refine ⟨t, ?_⟩
          rfl

/-- Every vertex occurs in the noninitial part of the kept cyclic listing. -/
private theorem mem_tail_keptVertexListing (start : Fin C.size)
    (marked : Fin C.size → Bool) (hstart : marked start = false)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) (z : V) :
    z ∈ (C.keptVertexListing M start marked).tail := by
  obtain ⟨l, hl⟩ := C.keptCoreVertices_eq_cons M start marked hstart hunique
  have hz := C.mem_keptCoreVertices M start marked hunique z
  rw [keptVertexListing, hl, List.cons_append, List.tail_cons]
  by_cases hroot : z = C.vertex start
  · subst z
    simp
  · rw [hl, List.mem_cons] at hz
    exact List.mem_append_left _ (hz.resolve_left hroot)

/-- The edge entering a cyclic position. -/
private def incoming (i : Fin C.size) : E :=
  C.edge (cyclicPrev C.size C.size_pos i)

/-- A pass is kept when its designated anchor is one of its two incident tour edges. -/
private def Keeps (anchor : V → E) (i : Fin C.size) : Prop :=
  incoming M C i = anchor (C.vertex i) ∨ C.edge i = anchor (C.vertex i)

/-- Mark every pass except the pass containing the designated anchor edge. -/
private noncomputable def anchorMarked (anchor : V → E) (i : Fin C.size) : Bool :=
  by
    classical
    exact decide (¬Keeps M C anchor i)
end CyclicCircuit
end EdgeIndexedMultigraph
end SimpleGraph
namespace SimpleGraph

/-- Consecutive tagged vertices are compatible with shortcutting exactly the marked ones. -/
private def MarkedSquareStep {V : Type*} (G : SimpleGraph V)
    (a b : V × Bool) : Prop :=
  match a.2, b.2 with
  | false, false => G.square.Adj a.1 b.1
  | false, true => G.Adj a.1 b.1
  | true, false => G.Adj a.1 b.1
  | true, true => False

/-- Remove marked occurrences and forget the tags. -/
private def unmarkedVertices {V : Type*} : List (V × Bool) → List V
  | [] => []
  | (v, false) :: l => v :: unmarkedVertices l
  | (_, true) :: l => unmarkedVertices l

/-- A marked middle occurrence never has equal neighbors. -/
private def MarkedNoBacktrack {V : Type*} : List (V × Bool) → Prop
  | a :: b :: c :: l => (b.2 = true → a.1 ≠ c.1) ∧ MarkedNoBacktrack (b :: c :: l)
  | _ => True

private theorem MarkedNoBacktrack.tail {V : Type*} {a : V × Bool}
    {l : List (V × Bool)} (h : MarkedNoBacktrack (a :: l)) :
    MarkedNoBacktrack l := by
  cases l with
  | nil => trivial
  | cons b l =>
      cases l with
      | nil => trivial
      | cons c l => exact h.2

/-- Removing isolated marked occurrences from a compatible chain leaves a chain in the graph
square. -/
private theorem MarkedSquareStep.isChain_unmarkedVertices {V : Type*} {G : SimpleGraph V}
    {l : List (V × Bool)} (hl : l.IsChain (MarkedSquareStep G))
    (hn : MarkedNoBacktrack l) :
    (unmarkedVertices l).IsChain G.square.Adj := by
  induction l with
  | nil => simp [unmarkedVertices]
  | cons a l ih =>
      cases a with
      | mk u marked =>
          cases marked with
          | false =>
              cases l with
              | nil => simp [unmarkedVertices]
              | cons b l =>
                  cases b with
                  | mk v marked' =>
                      have hparts := List.isChain_cons_cons.mp hl
                      cases marked' with
                      | false =>
                          rw [unmarkedVertices, unmarkedVertices]
                          apply List.isChain_cons_cons.mpr
                          exact ⟨hparts.1, ih hparts.2 hn.tail⟩
                      | true =>
                          cases l with
                          | nil => simp [unmarkedVertices]
                          | cons d l =>
                              cases d with
                              | mk w marked'' =>
                                  have hparts' := List.isChain_cons_cons.mp hparts.2
                                  cases marked'' with
                                  | false =>
                                      rw [unmarkedVertices, unmarkedVertices,
                                        unmarkedVertices]
                                      apply List.isChain_cons_cons.mpr
                                      refine ⟨⟨hn.1 rfl,
                                        Or.inr ⟨v, hparts.1, hparts'.1⟩⟩, ?_⟩
                                      exact ih hparts.2 hn.tail
                                  | true =>
                                      exact False.elim (by
                                        simpa [MarkedSquareStep] using hparts'.1)
          | true =>
              rw [unmarkedVertices]
              exact ih (List.IsChain.tail hl) hn.tail

end SimpleGraph

/-! ## EulerCircuitMarking -/

namespace SimpleGraph

namespace EdgeIndexedMultigraph

namespace CyclicCircuit

universe u v

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)

private theorem unmarkedVertices_map_positions (marked : Fin C.size → Bool)
    (positions : List (Fin C.size)) :
    unmarkedVertices
        (positions.map fun i ↦ (C.vertex i, marked i)) =
      positions.filterMap (C.keptVertex M marked) := by
  induction positions with
  | nil => rfl
  | cons i positions ih =>
      cases hi : marked i <;> simp [unmarkedVertices, keptVertex, hi, ih]

private theorem unmarkedVertices_append {l₁ l₂ : List (V × Bool)} :
    unmarkedVertices (l₁ ++ l₂) =
      unmarkedVertices l₁ ++ unmarkedVertices l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih =>
      rcases a with ⟨a, marked⟩
      cases marked <;> simp [unmarkedVertices, ih]

/-- Removing marked entries from the closed marked circuit gives its kept vertex listing. -/
private theorem unmarkedVertices_markedVertexListing (start : Fin C.size)
    (marked : Fin C.size → Bool) (hstart : marked start = false) :
    unmarkedVertices (C.markedVertexListing M start marked) =
      C.keptVertexListing M start marked := by
  rw [C.markedVertexListing_eq M start marked, unmarkedVertices_append,
    unmarkedVertices_map_positions, keptVertexListing, keptCoreVertices]
  simp [unmarkedVertices, hstart]

/-- Data ensuring that deleting the marked passes of a cyclic Euler circuit gives a rooted
Hamiltonian cycle in the square. -/
private structure SquareMarking [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) where
  start : Fin C.size
  root_start : C.vertex start = root
  marked : Fin C.size → Bool
  start_unmarked : marked start = false
  unique_unmarked : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false
  two_le_size : 2 ≤ C.size
  three_le_card : 3 ≤ Fintype.card V
  marked_square_chain :
    (C.markedVertexListing M start marked).IsChain (MarkedSquareStep G)
  no_backtrack : MarkedNoBacktrack (C.markedVertexListing M start marked)
  next_unmarked : marked (cyclicNext C.size C.size_pos start) = false
  prev_unmarked : marked (cyclicPrev C.size C.size_pos start) = false
  next_adj : G.Adj root (C.vertex (cyclicNext C.size C.size_pos start))
  prev_adj : G.Adj (C.vertex (cyclicPrev C.size C.size_pos start)) root

/-- Local edge conditions package a marking into the data needed for square shortcutting. -/
private noncomputable def SquareMarking.ofLocal [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (start : Fin C.size)
    (marked : Fin C.size → Bool) (hroot : C.vertex start = root)
    (hstart : marked start = false)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false)
    (hedge : ∀ i, marked i = false ∨
      marked (cyclicNext C.size C.size_pos i) = false)
    (hsquare : ∀ i, G.square.Adj (C.vertex i)
      (C.vertex (cyclicNext C.size C.size_pos i)))
    (horiginal : ∀ i, marked i = true ∨
      marked (cyclicNext C.size C.size_pos i) = true →
        G.Adj (C.vertex i) (C.vertex (cyclicNext C.size C.size_pos i)))
    (hnext : marked (cyclicNext C.size C.size_pos start) = false)
    (hprev : marked (cyclicPrev C.size C.size_pos start) = false)
    (hnextAdj : G.Adj root
      (C.vertex (cyclicNext C.size C.size_pos start)))
    (hprevAdj : G.Adj
      (C.vertex (cyclicPrev C.size C.size_pos start)) root)
    (hcard : 3 ≤ Fintype.card V) : C.SquareMarking M G root := by
  classical
  have hsize := C.three_le_size_of_unique_unmarked M marked hunique hcard
  refine {
    start := start
    root_start := hroot
    marked := marked
    start_unmarked := hstart
    unique_unmarked := hunique
    two_le_size := by omega
    three_le_card := hcard
    marked_square_chain := ?_
    no_backtrack := C.markedVertexListing_noBacktrack M start marked
      hunique hedge hcard
    next_unmarked := hnext
    prev_unmarked := hprev
    next_adj := hnextAdj
    prev_adj := hprevAdj }
  apply C.markedVertexListing_isChain M
  intro i
  let j := cyclicNext C.size C.size_pos i
  cases hi : marked i <;> cases hj : marked j
  · simpa [MarkedSquareStep, j, hi, hj] using hsquare i
  · simpa [MarkedSquareStep, j, hi, hj] using
      horiginal i (Or.inr hj)
  · simpa [MarkedSquareStep, j, hi, hj] using
      horiginal i (Or.inl hi)
  · rcases hedge i with h | h
    · simp [hi] at h
    · simp [j, hj] at h

/-- A compatible square marking produces the rooted cyclic listing obtained by lifting every
marked pass. -/
private noncomputable def SquareMarking.toStrongSquareCycleListing
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {root : V}
    (K : C.SquareMarking M G root) : G.StrongSquareCycleListing root := by
  classical
  let l := C.keptVertexListing M K.start K.marked
  let frontExists := C.keptVertexListing_eq_root_next M K.start K.marked
    K.two_le_size K.start_unmarked K.next_unmarked
  let middle := Classical.choose frontExists
  have hfront := Classical.choose_spec frontExists
  let backExists := C.keptVertexListing_eq_prev_root M K.start K.marked
    K.start_unmarked K.prev_unmarked
  let initial := Classical.choose backExists
  have hback := Classical.choose_spec backExists
  have hfront' : l = C.vertex K.start ::
      C.vertex (cyclicNext C.size C.size_pos K.start) ::
        middle ++ [C.vertex K.start] := by
    simpa only [l, middle] using hfront
  have hback' : l = initial ++
      [C.vertex (cyclicPrev C.size C.size_pos K.start), C.vertex K.start] := by
    simpa only [l, initial] using hback
  have htailNodup : l.tail.Nodup :=
    C.keptVertexListing_tail_nodup M K.start K.marked
      K.start_unmarked K.unique_unmarked
  have hmem : ∀ z, z ∈ l.tail :=
    C.mem_tail_keptVertexListing M K.start K.marked
      K.start_unmarked K.unique_unmarked
  have htailFinset : l.tail.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro z
    exact List.mem_toFinset.mpr (hmem z)
  have htailLength : l.tail.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup htailNodup, htailFinset,
      Finset.card_univ]
  have hlength : l.length = l.tail.length + 1 := by
    rw [hfront']
    simp
  have hcard : 3 ≤ Fintype.card V := K.three_le_card
  have hfour : 4 ≤ l.length := by omega
  have hchain : l.IsChain G.square.Adj := by
    have h := MarkedSquareStep.isChain_unmarkedVertices
      K.marked_square_chain K.no_backtrack
    rw [C.unmarkedVertices_markedVertexListing M K.start K.marked
      K.start_unmarked] at h
    exact h
  refine {
    vertices := l
    first := C.vertex (cyclicNext C.size C.size_pos K.start)
    last := C.vertex (cyclicPrev C.size C.size_pos K.start)
    frontRest := middle ++ [C.vertex K.start]
    backRest := initial
    front_shape := by simpa [K.root_start] using hfront'
    back_shape := by simpa only [K.root_start] using hback'
    four_le_length := hfour
    square_chain := hchain
    tail_nodup := htailNodup
    mem_tail := hmem
    first_adj := K.next_adj
    last_adj := K.prev_adj }

end CyclicCircuit
end EdgeIndexedMultigraph
end SimpleGraph
namespace SimpleGraph
namespace Walk
/-- The cycle-edge index anchored at a vertex when the two arcs from zero to `k` are
oriented away from zero. -/
private def splitCycleAnchorIndex {n : ℕ} [NeZero n] (k i : Fin n) : Fin n :=
  if i = 0 then 0 else if i.val ≤ k.val then i - 1 else i

/-- Original cycle edges used as anchors for the split transition system. -/
private def splitCycleAnchor (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k i : Fin c.length) : c.AugmentedTrailEdge cover q :=
  c.augmentedOriginalEdge cover q (splitCycleAnchorIndex k i)

/-- A split anchor never selects the distinguished edge when that edge carries a copy. -/
private theorem splitCycleAnchorIndex_ne_cut {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q)
    (i : Fin n) : splitCycleAnchorIndex cut.1 i ≠ cut.1 := by
  have hcut0 := cut.ne_zero q
  by_cases hi : i = 0
  · simpa [splitCycleAnchorIndex, hi] using hcut0.symm
  · by_cases hik : i.val ≤ cut.1.val
    · intro h
      have hval := congrArg Fin.val h
      rw [splitCycleAnchorIndex, ite_eq_right hi, ite_eq_left hik,
        Fin.val_sub_one_of_ne_zero hi] at hval
      have hipos : 0 < i.val := Nat.pos_of_ne_zero (fun h ↦ hi (Fin.ext h))
      omega
    · intro h
      have hval := congrArg Fin.val h
      simp [splitCycleAnchorIndex, hi, hik] at hval
      omega

/-- Split anchors in a multigraph with the distinguished parallel pair deleted. -/
private noncomputable def cutSplitCycleAnchor (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (i : Fin c.length) :
    c.CutAugmentedTrailEdge cover q cut :=
  c.cutOriginalEdge cover q cut (splitCycleAnchorIndex cut.1 i)
    (splitCycleAnchorIndex_ne_cut q cut i)

/-- Every edge surviving a parallel-pair deletion is an original cycle edge, a cover edge,
or an uncut copied cycle edge. -/
private theorem cutAugmentedTrailEdge_cases (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (e : c.CutAugmentedTrailEdge cover q cut) :
    (∃ (j : Fin c.length) (hj : j ≠ cut.1),
      e = c.cutOriginalEdge cover q cut j hj) ∨
    (∃ (D : c.outsideGraph.ConnectedComponent) (f : (cover D).Edge),
      e = c.cutCoverEdge cover q cut D f) ∨
    ∃ i : UncutActiveCycleCopy q cut,
      e = c.cutCopiedEdge cover q cut i := by
  rcases e with ⟨e, he⟩
  cases e with
  | inl e =>
      cases e with
      | inl j =>
          have hj : j.down ≠ cut.1 := by
            intro h
            apply he
            rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
            left
            apply congrArg Sum.inl
            apply congrArg Sum.inl
            exact ULift.ext _ _ h
          left
          exact ⟨j.down, hj, by rfl⟩
      | inr f =>
          right
          left
          exact ⟨f.1, f.2, by rfl⟩
  | inr f =>
      rcases f with ⟨j, r⟩
      have hcopy : q.copies j = 1 := by
        have hpos : 0 < q.copies j := Nat.pos_of_ne_zero (by
          intro hzero
          simpa [hzero] using r.isLt)
        have hlt := q.copies_lt_two j
        omega
      let active : ActiveCycleCopy q := ⟨j, hcopy⟩
      have hne : active.1 ≠ cut.1 := by
        intro h
        have hj : j = cut.1 := h
        subst j
        apply he
        rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
        right
        apply congrArg Sum.inr
        congr 1
        apply Fin.ext
        omega
      right
      right
      let i : UncutActiveCycleCopy q cut := ⟨active, hne⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inr
      dsimp only [i, active]
      congr 1
      apply Fin.ext
      omega

end Walk
namespace EdgeIndexedMultigraph
namespace IndexedWalk
end IndexedWalk
namespace CyclicCircuit
end CyclicCircuit
end EdgeIndexedMultigraph
namespace Walk
end Walk
end SimpleGraph
namespace SimpleGraph
/-- The vertex-rooted strengthening of Fleischner's theorem, indexed by the number of
vertices for strong induction. -/
private theorem IsVertexConnected.hasStrongSquareCycle_card
    (n : ℕ) {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsVertexConnected 2) (hcard : Fintype.card V = n) (x : V) :
    G.HasStrongSquareCycle x := by
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      classical
      have hn3 : 3 ≤ n := by
        have := hG.card_gt
        omega
      by_cases hn : n = 3
      · apply hG.hasStrongSquareCycle_of_card_eq_three
        omega
      · obtain ⟨c, hc, y, hyx, hbound⟩ := hG.exists_cycle_bound_vertex x
        have hclength : 0 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
        let _ : NeZero c.length := ⟨Nat.ne_of_gt hclength⟩
        let k := hc.finLengthEquivSupport.symm ⟨y, hbound.1⟩
        have hky : c.getVert k = y := by
          apply (hc.finLengthEquivSupport_apply k).symm.trans
          simpa only [k] using congrArg Subtype.val
            (hc.finLengthEquivSupport.apply_symm_apply ⟨y, hbound.1⟩)
        have hk0 : k ≠ 0 := by
          intro hk
          apply hyx
          have hkval : k.val = 0 := congrArg Fin.val hk
          calc
            y = c.getVert k := hky.symm
            _ = c.getVert 0 := congrArg c.getVert hkval
            _ = x := c.getVert_zero
        have hboundK : c.IsBoundVertex (c.getVert k) := hky ▸ hbound
        let cover : (D : c.outsideGraph.ConnectedComponent) →
            c.ComponentTrailCover D := fun D ↦ Classical.choice (by
          by_cases hD : (c.componentVertices D).ncard = 1
          · exact SimpleGraph.Walk.IsVertexConnected.singletonComponentTrailCover
              hG c D hD
          · have hDpos : 0 < (c.componentVertices D).ncard :=
              (Set.ncard_pos).mpr (c.componentVertices_nonempty D)
            have hDtwo : 1 < (c.componentVertices D).ncard := by omega
            let _ : Fintype (c.componentVertices D) := Fintype.ofFinite _
            have hcontract := hc.component_contractOutside_isVertexConnected hG D hDtwo
            have hltCard : Fintype.card (Option (c.componentVertices D)) < n := by
              have hlt := hc.card_component_contractOutside_lt D
              rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard] at hlt
              exact hlt
            have hstrong : (G.contractOutside (c.componentVertices D)).HasStrongSquareCycle
                none := by
              apply ih (Fintype.card (Option (c.componentVertices D))) hltCard
                hcontract rfl
            exact SimpleGraph.Walk.ComponentTrailCover.exists_of_contractOutside_strongCycle
              D hstrong)
        apply c.hasStrongSquareCycle_of_componentTrailCovers hc cover k hk0 hboundK
        omega
end SimpleGraph
