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
import Abbrev.Combinatorics.SimpleGraph.FleischnerStrong.Part9
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

/-- A retained original edge in the cut augmented multigraph. -/
noncomputable def cutOriginalEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (j : Fin c.length) (hj : j ≠ cut.1) :
    c.CutAugmentedTrailEdge cover q cut := by
  refine ⟨c.augmentedOriginalEdge cover q j, ?_⟩
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simpa [cycleParallelPair, augmentedOriginalEdge] using hj
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]

/-- A retained copied edge in the cut augmented multigraph. -/
noncomputable def cutCopiedEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (i : UncutActiveCycleCopy q cut) :
    c.CutAugmentedTrailEdge cover q cut := by
  refine ⟨c.augmentedCopiedEdge cover q i.1.2, ?_⟩
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]
  · intro h
    have hind := congrArg
      (fun e : c.AugmentedTrailEdge cover q ↦ match e with
        | Sum.inl _ => none
        | Sum.inr e => some e.1)
      h
    apply i.2
    exact Option.some.inj
      (by simpa [cycleParallelPair, augmentedCopiedEdge] using hind)

/-- A component-cover edge retained after deleting one cycle-edge pair. -/
noncomputable def cutCoverEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (D : c.outsideGraph.ConnectedComponent)
    (e : (cover D).Edge) : c.CutAugmentedTrailEdge cover q cut := by
  refine ⟨c.augmentedCoverEdge cover q D e, ?_⟩
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  simp [cycleParallelPair, augmentedCoverEdge, augmentedOriginalEdge,
    augmentedCopiedEdge]

end Walk
end SimpleGraph
