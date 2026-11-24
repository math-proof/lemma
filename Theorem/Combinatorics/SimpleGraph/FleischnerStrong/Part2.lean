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
public import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part5


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

theorem nontrivialCoverEnds_square_adj [DecidableEq V]
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

end Walk
end SimpleGraph
