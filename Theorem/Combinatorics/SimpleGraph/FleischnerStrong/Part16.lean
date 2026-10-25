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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part28
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

/-- The paired original/copy edge identities are all distinct. -/
theorem splitCycleTransition_edge_injective (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    Function.Injective ((c.augmentedTrailMultigraph cover q).transitionEdge
      (c.splitCycleTransition hc cover q k hlast)) := by
  intro a b hab
  rcases a with ⟨i, side⟩
  rcases b with ⟨j, side'⟩
  have hpartner := splitPartnerIndex_injective_on_active q k hlast
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have hside' : side' = 0 ∨ side' = 1 := by
    have hval : side'.val = 0 ∨ side'.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hside with rfl | rfl <;> rcases hside' with rfl | rfl
  · have hij : splitPartnerIndex k i.1 = splitPartnerIndex k j.1 := by
      simpa [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge] using hab
    have hij' : i = j := hpartner hij
    subst j
    rfl
  · simp [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge,
      augmentedCopiedEdge] at hab
  · simp [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge,
      augmentedCopiedEdge] at hab
  · have hij : i.1 = j.1 := by
      simp only [EdgeIndexedMultigraph.transitionEdge, Fin.isValue, one_ne_zero,
        ↓reduceIte, splitCycleTransition_right, augmentedCopiedEdge,
        Sum.inr.injEq, Sigma.mk.injEq] at hab
      exact hab.1
    apply Prod.ext
    · exact Subtype.ext hij
    · rfl

end Walk
end SimpleGraph
