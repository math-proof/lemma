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
import Instance.Combinatorics.SimpleGraph.FleischnerStrong.Part3
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

/-- Simultaneously compress a family of forced transitions. -/
def compressTransitions {T : Type*} (transition : T → M.EdgeTransition) :
    EdgeIndexedMultigraph V (M.CompressedTransitionEdge transition) where
  ends
    | Sum.inl e => M.ends e.1
    | Sum.inr t => s((transition t).before, (transition t).after)
  loopless := by
    intro e v he
    cases e with
    | inl e => exact M.loopless e.1 v he
    | inr t =>
        rcases Sym2.eq_iff.mp he with h | h
        · exact (transition t).before_ne_after (h.1.trans h.2.symm)
        · exact (transition t).before_ne_after (h.1.trans h.2.symm)

noncomputable def edgePartitionEquiv {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) :
    E ≃ M.UnpairedTransitionEdge transition ⊕ (T × Fin 2) := by
  classical
  exact
    (Equiv.sumCompl (fun e ↦ e ∈ Set.range (M.transitionEdge transition))).symm |>.trans
      (Equiv.sumCongr (Equiv.ofInjective _ hinj).symm (Equiv.refl _)) |>.trans
      (Equiv.sumComm _ _)

noncomputable def incidenceWeight (v : V) (e : E) : ZMod 2 := by
  classical
  exact if M.Inc v e then 1 else 0

/-- The original edge identities represented by one compressed edge. -/
def transitionExpansionEdges {T : Type*}
    (transition : T → M.EdgeTransition) :
    M.CompressedTransitionEdge transition → List E
  | Sum.inl e => [e.1]
  | Sum.inr t => [(transition t).left, (transition t).right]

/-- Two edge identities occur consecutively, in either order, in an edge list. -/
def EdgesAdjacent (a b : E) (l : List E) : Prop :=
  ∃ before after, l = before ++ a :: b :: after ∨
    l = before ++ b :: a :: after

end EdgeIndexedMultigraph
end SimpleGraph
