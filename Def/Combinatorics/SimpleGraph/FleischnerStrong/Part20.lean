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
import Instance.Combinatorics.SimpleGraph.FleischnerStrong.Part4
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

/-- Delete both edge identities in a parallel pair. -/
def eraseParallelPair (p : M.ParallelPair) :
    EdgeIndexedMultigraph V (M.ErasedParallelPair p) where
  ends e := M.ends e.1
  loopless e := M.loopless e.1

/-- Regard a transition whose edges survive deletion as a transition in the erased multigraph. -/
def ParallelPair.liftTransition {M : EdgeIndexedMultigraph V E}
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

noncomputable def parallelPairPartition (p : M.ParallelPair) :
    E ≃ M.ErasedParallelPair p ⊕ Fin 2 := by
  classical
  exact
    (Equiv.sumCompl (fun e ↦ e ∈ Set.range p.edge)).symm |>.trans
      (Equiv.sumCongr (Equiv.ofInjective _ p.edge_injective).symm (Equiv.refl _)) |>.trans
      (Equiv.sumComm _ _)

end EdgeIndexedMultigraph
end SimpleGraph
