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
public import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part25


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
