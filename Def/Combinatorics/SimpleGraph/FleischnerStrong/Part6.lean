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
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part2
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
