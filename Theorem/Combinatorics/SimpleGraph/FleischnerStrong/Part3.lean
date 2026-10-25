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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part6
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

theorem cycleIncidenceToCover_source [DecidableEq V]
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

theorem coverIncidenceToCycle_val [DecidableEq V]
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

theorem coverIncidenceToCycle_cycleIncidenceToCover [DecidableEq V]
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

theorem badCycleIncidence_vertex_eq_of_mem [DecidableEq V]
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

theorem cycleIncidenceToCover_coverIncidenceToCycle [DecidableEq V]
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

end Walk
end SimpleGraph
