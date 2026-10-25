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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part35
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

/-- Every edge surviving a parallel-pair deletion is an original cycle edge, a cover edge,
or an uncut copied cycle edge. -/
theorem cutAugmentedTrailEdge_cases (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (e : c.CutAugmentedTrailEdge cover q cut) :
    (∃ (j : Fin c.length) (hj : j ≠ cut.1),
      e = c.cutOriginalEdge cover q cut j hj) ∨
    (∃ (D : c.outsideGraph.ConnectedComponent) (f : (cover D).Edge),
      e = c.cutCoverEdge cover q cut D f) ∨
    ∃ i : UncutActiveCycleCopy q cut,
      e = c.cutCopiedEdge cover q cut i := by
  rcases e with ⟨e, he⟩
  cases e with
  | inl e =>
      cases e with
      | inl j =>
          have hj : j.down ≠ cut.1 := by
            intro h
            apply he
            rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
            left
            apply congrArg Sum.inl
            apply congrArg Sum.inl
            exact ULift.ext _ _ h
          left
          exact ⟨j.down, hj, by rfl⟩
      | inr f =>
          right
          left
          exact ⟨f.1, f.2, by rfl⟩
  | inr f =>
      rcases f with ⟨j, r⟩
      have hcopy : q.copies j = 1 := by
        have hpos : 0 < q.copies j := Nat.pos_of_ne_zero (by
          intro hzero
          simpa [hzero] using r.isLt)
        have hlt := q.copies_lt_two j
        omega
      let active : ActiveCycleCopy q := ⟨j, hcopy⟩
      have hne : active.1 ≠ cut.1 := by
        intro h
        have hj : j = cut.1 := h
        subst j
        apply he
        rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
        right
        apply congrArg Sum.inr
        congr 1
        apply Fin.ext
        omega
      right
      right
      let i : UncutActiveCycleCopy q cut := ⟨active, hne⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inr
      dsimp only [i, active]
      congr 1
      apply Fin.ext
      omega

end Walk

namespace EdgeIndexedMultigraph

namespace IndexedWalk

end IndexedWalk

namespace CyclicCircuit

end CyclicCircuit

end EdgeIndexedMultigraph

namespace Walk

end Walk

end SimpleGraph

namespace SimpleGraph

/-- The vertex-rooted strengthening of Fleischner's theorem, indexed by the number of
vertices for strong induction. -/
theorem IsVertexConnected.hasStrongSquareCycle_card
    (n : ℕ) {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsVertexConnected 2) (hcard : Fintype.card V = n) (x : V) :
    G.HasStrongSquareCycle x := by
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      classical
      have hn3 : 3 ≤ n := by
        have := hG.card_gt
        omega
      by_cases hn : n = 3
      · apply hG.hasStrongSquareCycle_of_card_eq_three
        omega
      · obtain ⟨c, hc, y, hyx, hbound⟩ := hG.exists_cycle_bound_vertex x
        have hclength : 0 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
        let _ : NeZero c.length := ⟨Nat.ne_of_gt hclength⟩
        let k := hc.finLengthEquivSupport.symm ⟨y, hbound.1⟩
        have hky : c.getVert k = y := by
          apply (hc.finLengthEquivSupport_apply k).symm.trans
          simpa only [k] using congrArg Subtype.val
            (hc.finLengthEquivSupport.apply_symm_apply ⟨y, hbound.1⟩)
        have hk0 : k ≠ 0 := by
          intro hk
          apply hyx
          have hkval : k.val = 0 := congrArg Fin.val hk
          calc
            y = c.getVert k := hky.symm
            _ = c.getVert 0 := congrArg c.getVert hkval
            _ = x := c.getVert_zero
        have hboundK : c.IsBoundVertex (c.getVert k) := hky ▸ hbound
        let cover : (D : c.outsideGraph.ConnectedComponent) →
            c.ComponentTrailCover D := fun D ↦ Classical.choice (by
          by_cases hD : (c.componentVertices D).ncard = 1
          · exact SimpleGraph.Walk.IsVertexConnected.singletonComponentTrailCover
              hG c D hD
          · have hDpos : 0 < (c.componentVertices D).ncard :=
              (Set.ncard_pos).mpr (c.componentVertices_nonempty D)
            have hDtwo : 1 < (c.componentVertices D).ncard := by omega
            let _ : Fintype (c.componentVertices D) := Fintype.ofFinite _
            have hcontract := hc.component_contractOutside_isVertexConnected hG D hDtwo
            have hltCard : Fintype.card (Option (c.componentVertices D)) < n := by
              have hlt := hc.card_component_contractOutside_lt D
              rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard] at hlt
              exact hlt
            have hstrong : (G.contractOutside (c.componentVertices D)).HasStrongSquareCycle
                none := by
              apply ih (Fintype.card (Option (c.componentVertices D))) hltCard
                hcontract rfl
            exact SimpleGraph.Walk.ComponentTrailCover.exists_of_contractOutside_strongCycle
              D hstrong)
        apply c.hasStrongSquareCycle_of_componentTrailCovers hc cover k hk0 hboundK
        omega

end SimpleGraph
