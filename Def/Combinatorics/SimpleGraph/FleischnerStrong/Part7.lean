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
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part3
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

noncomputable def cycleCoverIncidenceEquiv [DecidableEq V]
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

def cycleCoverEdgeOfMem {S : Set V}
    (p : (G.contractOutside S).square.Walk none none) {a b : Option S}
    (he : s(a, b) ∈ p.edges) : CycleCoverEdge p := by
  refine ⟨s(a, b), ?_⟩
  change s(a, b) ∈ p.toSubgraph.spanningCoe.edgeSet
  rw [Subgraph.edgeSet_spanningCoe, p.mem_edges_toSubgraph]
  exact he

end Walk
end SimpleGraph
