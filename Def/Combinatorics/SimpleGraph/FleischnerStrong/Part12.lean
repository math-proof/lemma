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
public import Instance.Combinatorics.SimpleGraph.FleischnerStrong.Part2


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

variable {V : Type*} {G : SimpleGraph V} {x : V}

/-- The indexed multigraph of the prescribed parallel cycle-edge copies. -/
def cycleCopyMultigraph (c : G.Walk x x) [NeZero c.length]
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

end Walk
end SimpleGraph
