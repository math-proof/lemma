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
public import Abbrev.Combinatorics.SimpleGraph.FleischnerStrong.Part9


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
