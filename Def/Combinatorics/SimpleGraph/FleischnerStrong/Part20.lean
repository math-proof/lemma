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
public import Instance.Combinatorics.SimpleGraph.FleischnerStrong.Part4


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
