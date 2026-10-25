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
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part18
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

noncomputable def cutSplitCompressedCoverHom (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (D : c.outsideGraph.ConnectedComponent) :
    (cover D).multigraph.underlying →g
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying where
  toFun := id
  map_rel' := by
    intro u v huv
    obtain ⟨e, he⟩ := (cover D).multigraph.underlying_adj.mp huv
    let edge := c.cutCoverEdge cover q cut D e
    apply (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying_adj.mpr
    refine ⟨Sum.inl ⟨edge, ?_⟩, ?_⟩
    · rintro ⟨⟨i, side⟩, hi⟩
      have hval := congrArg Subtype.val hi
      have hside : side = 0 ∨ side = 1 := by
        have hsval : side.val = 0 ∨ side.val = 1 := by omega
        exact hsval.imp Fin.ext Fin.ext
      rcases hside with rfl | rfl
      · have hcycle : c.augmentedCoverEdge cover q D e =
            c.augmentedOriginalEdge cover q (splitPartnerIndex cut.1 i.1.1) := by
          simpa [edge, EdgeIndexedMultigraph.transitionEdge,
            cutSplitCycleTransition, EdgeIndexedMultigraph.ParallelPair.liftTransition,
            cutCoverEdge, cutOriginalEdge] using hval.symm
        simp [augmentedCoverEdge, augmentedOriginalEdge] at hcycle
      · have hcycle : c.augmentedCoverEdge cover q D e =
            c.augmentedCopiedEdge cover q i.1.2 := by
          simpa [edge, EdgeIndexedMultigraph.transitionEdge,
            cutSplitCycleTransition, EdgeIndexedMultigraph.ParallelPair.liftTransition,
            cutCoverEdge, cutCopiedEdge] using hval.symm
        simp [augmentedCoverEdge, augmentedCopiedEdge] at hcycle
    · exact (c.cutAugmentedTrailMultigraph_ends_cover cover q cut D e).trans he

end Walk

end SimpleGraph

namespace SimpleGraph

namespace Walk

end Walk

end SimpleGraph

namespace SimpleGraph

namespace EdgeIndexedMultigraph

/-- The next position in a nonempty finite cyclic order. -/
def cyclicNext (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- The previous position in a nonempty finite cyclic order. -/
def cyclicPrev (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩

end EdgeIndexedMultigraph
end SimpleGraph
