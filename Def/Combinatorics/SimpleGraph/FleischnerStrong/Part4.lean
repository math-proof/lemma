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
public import Abbrev.Combinatorics.SimpleGraph.FleischnerStrong.Part2


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

def NontrivialCoverEdge.sourceCycleEdge {S : Set V}
    {p : (G.contractOutside S).square.Walk none none} :
    NontrivialCoverEdge p → CycleCoverEdge p
  | Sum.inl e => e.1
  | Sum.inr i => i.edge

noncomputable def goodCycleCoverLeft {S : Set V}
    {p : (G.contractOutside S).square.Walk none none}
    (e : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e}) : S :=
  e.property.choose

noncomputable def goodCycleCoverRight {S : Set V}
    {p : (G.contractOutside S).square.Walk none none}
    (e : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e}) : S :=
  e.property.choose_spec.choose

end Walk
end SimpleGraph
