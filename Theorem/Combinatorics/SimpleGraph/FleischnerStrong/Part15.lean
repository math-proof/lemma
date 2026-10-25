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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part27
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

theorem splitPartnerIndex_ne_cut {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q)
    (hlast : q.copies (cycleLastIndex n) = 0)
    (i : UncutActiveCycleCopy q cut) :
    splitPartnerIndex cut.1 i.1.1 ≠ cut.1 := by
  intro h
  have hval := congrArg Fin.val h
  rw [splitPartnerIndex_val_on_active q cut.1 hlast i.1] at hval
  have hipos : 0 < i.1.1.val :=
    Nat.pos_of_ne_zero (fun hzero ↦ i.1.ne_zero q (Fin.ext hzero))
  by_cases hlt : i.1.1.val < cut.1.val
  · simp [hlt] at hval
    omega
  · simp [hlt] at hval
    have hneval : i.1.1.val ≠ cut.1.val := fun heq ↦ i.2 (Fin.ext heq)
    omega

theorem splitCycleTransition_left_survives_cut (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) :
    (c.splitCycleTransition hc cover q cut.1 hlast i.1).left ∉
      Set.range (c.cycleParallelPair cover q cut.2).edge := by
  rw [c.splitCycleTransition_left]
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simpa [cycleParallelPair, augmentedOriginalEdge] using
      splitPartnerIndex_ne_cut q cut hlast i
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]

theorem splitCycleTransition_right_survives_cut (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) :
    (c.splitCycleTransition hc cover q cut.1 hlast i.1).right ∉
      Set.range (c.cycleParallelPair cover q cut.2).edge := by
  rw [c.splitCycleTransition_right]
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]
  · intro h
    exact i.2 (augmentedCopiedEdge_index_eq c cover q i.1.2 cut.2 h)

end Walk
end SimpleGraph
