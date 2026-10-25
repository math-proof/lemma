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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part25
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

/-- The forward closing-edge-cut transitions are pairwise edge-disjoint. -/
theorem forwardLastCutCycleTransition_edge_injective (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) :
    Function.Injective
      ((c.cutAugmentedTrailMultigraph cover q (lastActiveCycleCopy q hlast)).transitionEdge
        (c.forwardLastCutCycleTransition hc cover q hlast)) := by
  intro a b hab
  rcases a with ⟨i, side⟩
  rcases b with ⟨j, side'⟩
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have hside' : side' = 0 ∨ side' = 1 := by
    have hval : side'.val = 0 ∨ side'.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hside with rfl | rfl <;> rcases hside' with rfl | rfl
  · have hval := congrArg Subtype.val hab
    have hind : i.1.1 - 1 = j.1.1 - 1 := by
      simpa [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
        cutOriginalEdge, augmentedOriginalEdge] using hval
    have hij : i = j := by
      apply Subtype.ext
      apply Subtype.ext
      exact sub_left_injective hind
    subst j
    rfl
  · have hval := congrArg Subtype.val hab
    simp [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
      cutOriginalEdge, cutCopiedEdge, augmentedOriginalEdge, augmentedCopiedEdge] at hval
  · have hval := congrArg Subtype.val hab
    simp [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
      cutOriginalEdge, cutCopiedEdge, augmentedOriginalEdge, augmentedCopiedEdge] at hval
  · have hval := congrArg Subtype.val hab
    have hind : i.1.1 = j.1.1 := by
      apply augmentedCopiedEdge_index_eq c cover q i.1.2 j.1.2
      simpa [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
        cutCopiedEdge] using hval
    have hij : i = j := by
      apply Subtype.ext
      exact Subtype.ext hind
    subst j
    rfl

end Walk
end SimpleGraph
