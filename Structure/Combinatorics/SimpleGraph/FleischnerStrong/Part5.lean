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
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part9
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/

/-! ## CycleComplement -/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

/-- One expanded transition, together with its edge-list permutation. -/
structure PrependedTransition [DecidableEq V] {T : Type*}
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

end EdgeIndexedMultigraph
end SimpleGraph
