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
import Structure.Combinatorics.SimpleGraph.FleischnerStrong.Part6
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

/-- Expand a compressed walk while retaining its edge-list permutation. -/
def expandTransitionsWithEdges [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {u v : V} :
    (p : (M.compressTransitions transition).IndexedWalk u v) →
      M.ExpandedTransitions transition p
  | .nil w => ⟨.nil w, by simp, by simp⟩
  | .cons e he p =>
      let tail := expandTransitionsWithEdges transition p
      let step := M.prependExpandedTransition transition e he tail.walk
      ⟨step.walk, step.edges_perm.trans (tail.edges_perm.append_left _), by
        intro t ht
        rw [IndexedWalk.edges_cons] at ht
        rcases List.mem_cons.mp ht with het | ht
        · cases e with
          | inl e => simp at het
          | inr t' =>
              have htt : t' = t := Sum.inr.inj het.symm
              subst t'
              rcases step.edges_shape with h | h
              · rw [h]
                exact ⟨[], tail.walk.edges, Or.inl rfl⟩
              · rw [h]
                exact ⟨[], tail.walk.edges, Or.inr rfl⟩
        · have htail := tail.edges_adjacent t ht
          cases e with
          | inl e =>
              rw [step.edges_shape]
              exact htail.cons e.1
          | inr t' =>
              rcases step.edges_shape with h | h
              · rw [h]
                exact (htail.cons (transition t').right).cons
                  (transition t').left
              · rw [h]
                exact (htail.cons (transition t').left).cons
                  (transition t').right⟩

/-- Expand every temporary transition edge back to its two original indexed edges. -/
def expandTransitions [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {u v : V}
    (p : (M.compressTransitions transition).IndexedWalk u v) : M.IndexedWalk u v :=
  (M.expandTransitionsWithEdges transition p).walk

/-- Map an original edge to the compressed edge that accounts for it. -/
noncomputable def transitionOwner {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (e : E) :
    M.CompressedTransitionEdge transition :=
  match M.edgePartitionEquiv transition hinj e with
  | Sum.inl f => Sum.inl f
  | Sum.inr p => Sum.inr p.1

end EdgeIndexedMultigraph
end SimpleGraph
