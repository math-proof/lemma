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
public import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part16


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

/-- The augmented trail multigraph after the two-arc transitions are compressed. -/
noncomputable def splitCompressedMultigraph (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :=
  (c.augmentedTrailMultigraph cover q).compressTransitions
    (c.splitCycleTransition hc cover q k hlast)

/-- The closing-edge-cut multigraph after its forward transitions are compressed. -/
noncomputable def forwardLastCutCompressedMultigraph (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) :=
  (c.cutAugmentedTrailMultigraph cover q (lastActiveCycleCopy q hlast)).compressTransitions
    (c.forwardLastCutCycleTransition hc cover q hlast)

/-- The distinguished-edge-cut multigraph after its two-arc transitions are compressed. -/
noncomputable def cutSplitCompressedMultigraph (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0) :=
  (c.cutAugmentedTrailMultigraph cover q cut).compressTransitions
    (c.cutSplitCycleTransition hc cover q cut hlast)

end Walk
end SimpleGraph
