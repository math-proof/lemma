/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteCutoff
import Mathlib.Combinatorics.SimpleGraph.Metric
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFiniteBoundaryCutoff.Part2


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

theorem isingFiniteGraphDistanceToBoundary_le_dist
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (x b : V) (hb : boundary b) :
    isingFiniteGraphDistanceToBoundary G boundary hboundary x ≤ G.dist x b := by
  classical
  unfold isingFiniteGraphDistanceToBoundary
  apply Finset.min'_le
  apply Finset.mem_image.mpr
  exact ⟨b, by simp [isingFiniteGraphBoundaryVertices, hb], rfl⟩

theorem isingFiniteGraphDistanceToBoundary_eq_zero
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (x : V) (hx : boundary x) :
    isingFiniteGraphDistanceToBoundary G boundary hboundary x = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using isingFiniteGraphDistanceToBoundary_le_dist
    G boundary hboundary x x hx

theorem isingFiniteGraphDistanceToBoundary_exists_eq_dist
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (x : V) :
    ∃ b, boundary b ∧
      isingFiniteGraphDistanceToBoundary G boundary hboundary x = G.dist x b := by
  classical
  let B := isingFiniteGraphBoundaryVertices boundary
  have hB : B.Nonempty :=
    isingFiniteGraphBoundaryVertices_nonempty boundary hboundary
  have hmem := Finset.min'_mem (B.image (G.dist x)) (hB.image _)
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hmem
  refine ⟨b, ?_, ?_⟩
  · simpa [B, isingFiniteGraphBoundaryVertices] using hb
  · unfold isingFiniteGraphDistanceToBoundary
    exact heq.symm


theorem isingFiniteGraphDistanceToBoundary_adj
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) {x y : V} (hxy : G.Adj x y) :
    isingFiniteGraphDistanceToBoundary G boundary hboundary y ≤
        isingFiniteGraphDistanceToBoundary G boundary hboundary x + 1 ∧
      isingFiniteGraphDistanceToBoundary G boundary hboundary x ≤
        isingFiniteGraphDistanceToBoundary G boundary hboundary y + 1 := by
  constructor
  · obtain ⟨b, hb, hxb⟩ :=
      isingFiniteGraphDistanceToBoundary_exists_eq_dist
        G boundary hboundary x
    have hstep := hxy.diff_dist_adj (u := b)
    have hyb : G.dist y b ≤ G.dist x b + 1 := by
      rw [G.dist_comm (u := y) (v := b), G.dist_comm (u := x) (v := b)]
      rcases hstep with hstep | hstep | hstep <;> omega
    exact (isingFiniteGraphDistanceToBoundary_le_dist
      G boundary hboundary y b hb).trans (hxb.symm ▸ hyb)
  · obtain ⟨b, hb, hyb⟩ :=
      isingFiniteGraphDistanceToBoundary_exists_eq_dist
        G boundary hboundary y
    have hstep := hxy.symm.diff_dist_adj (u := b)
    have hxb : G.dist x b ≤ G.dist y b + 1 := by
      rw [G.dist_comm (u := x) (v := b), G.dist_comm (u := y) (v := b)]
      rcases hstep with hstep | hstep | hstep <;> omega
    exact (isingFiniteGraphDistanceToBoundary_le_dist
      G boundary hboundary x b hb).trans (hyb.symm ▸ hxb)


end
end StatMech.Universality
