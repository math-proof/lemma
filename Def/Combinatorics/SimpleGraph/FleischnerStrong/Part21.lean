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
public import Abbrev.Combinatorics.SimpleGraph.FleischnerStrong.Part7


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

/-- A trail system augmented by arbitrary parity-correcting cycle copies. -/
noncomputable def augmentedTrailMultigraph (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :
    EdgeIndexedMultigraph V (c.AugmentedTrailEdge cover q) :=
  (c.trailSystemMultigraph cover).disjointSum (c.cycleCopyMultigraph q)

/-- The original cycle edge at an index, viewed in the augmented trail multigraph. -/
def augmentedOriginalEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (i : Fin c.length) : c.AugmentedTrailEdge cover q :=
  Sum.inl (Sum.inl (ULift.up i))

/-- The unique copied edge at an index whose copy count is one. -/
def augmentedCopiedEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    {i : Fin c.length} (hi : q.copies i = 1) : c.AugmentedTrailEdge cover q :=
  Sum.inr ⟨i, ⟨0, by omega⟩⟩

/-- A component-cover edge viewed in the augmented trail multigraph. -/
def augmentedCoverEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (D : c.outsideGraph.ConnectedComponent) (e : (cover D).Edge) :
    c.AugmentedTrailEdge cover q :=
  Sum.inl (Sum.inr ⟨D, e⟩)

/-- An original cycle edge and its parity-correcting copy form a parallel pair. -/
noncomputable def cycleParallelPair (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    {i : Fin c.length} (hi : q.copies i = 1) :
    (c.augmentedTrailMultigraph cover q).ParallelPair where
  first := c.augmentedOriginalEdge cover q i
  second := c.augmentedCopiedEdge cover q hi
  ne := by simp [augmentedOriginalEdge, augmentedCopiedEdge]
  ends_eq := by
    rw [c.augmentedTrailMultigraph_ends_original,
      c.augmentedTrailMultigraph_ends_copy]

end Walk
end SimpleGraph
