module
public import Def.Combinatorics.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.VertexConnectivity
public import Theorem.SimpleGraph.Contraction
public import Theorem.SimpleGraph.EdgeIndexedMultigraph
public import Theorem.SimpleGraph.Riha
public import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
public import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
public import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
public import Def.Combinatorics.SimpleGraph.Riha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.ZMod.Basic
public import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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

noncomputable def nontrivialCoverMultigraph [DecidableEq V]
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

noncomputable def cycleIncidenceToCover [DecidableEq V]
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

noncomputable def coverIncidenceToCycle [DecidableEq V]
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

end Walk
end SimpleGraph
