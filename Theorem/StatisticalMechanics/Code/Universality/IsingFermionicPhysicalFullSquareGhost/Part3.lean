/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteGhostComparison.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRangeTransfer
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part3
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareFullVertexGhostMultiplicity_pos_iff
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    0 < fkIsingSquareFullVertexGhostMultiplicity n x ↔
      x.1 1 = -(n : Int) ∨ x.1 0 = (n : Int) ∨
        x.1 1 = (n : Int) := by
  unfold fkIsingSquareFullVertexGhostMultiplicity
  by_cases hs : x.1 1 = -(n : Int) <;>
    by_cases he : x.1 0 = (n : Int) <;>
    by_cases hnorth : x.1 1 = (n : Int) <;>
    simp [hs, he, hnorth]

theorem fkIsingSquareFullFaceGhostMultiplicity_pos_iff
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    0 < fkIsingSquareFullFaceGhostMultiplicity n c ↔ c.1.1 = 0 := by
  unfold fkIsingSquareFullFaceGhostMultiplicity
  by_cases h : c.1.1 = 0 <;> simp [h]


theorem fkIsingSquareFullVertex_boundary_fixed_or_ghost
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareBoxBoundary n x) :
    fkIsingSquareFullVertexFixedBoundary n x ∨
      0 < fkIsingSquareFullVertexGhostMultiplicity n x := by
  rcases hx with ⟨i, hi⟩
  rw [fkIsingSquareFullVertexGhostMultiplicity_pos_iff]
  fin_cases i
  · rcases Int.natAbs_eq_iff.mp hi with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
  · rcases Int.natAbs_eq_iff.mp hi with h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)


theorem fkIsingSquareFullVertex_reaches_fixed_or_ghost
    (n : Nat) :
    ∀ x : FKIsingSquareFullVertexNode n, ∃ b,
      (fkIsingSquareFullVertexFixedBoundary n b ∨
          0 < fkIsingSquareFullVertexGhostMultiplicity n b) ∧
        (fkIsingSquareFullVertexGraph n).Reachable x b := by
  intro x
  refine ⟨fkIsingSquareMarkedA n, Or.inl ?_, ?_⟩
  · exact fkIsingSquareMarkedA_mem_wiredArc n
  · exact StatMech.FrontierB.boxGraph_preconnected 2 n x
      (fkIsingSquareMarkedA n)


theorem fkIsingSquareFullFace_reaches_fixed_or_ghost
    (n : Nat) :
    ∀ c : FKIsingSquareFullFaceNode n, ∃ b,
      (fkIsingSquareFullFaceFixedBoundary n b ∨
          0 < fkIsingSquareFullFaceGhostMultiplicity n b) ∧
        (fkIsingSquareFullFaceGraph n).Reachable c b := by
  let P : Nat → Prop := fun k ↦
    ∀ c : FKIsingSquareFullFaceNode n, c.2.1 = k → ∃ b,
      (fkIsingSquareFullFaceFixedBoundary n b ∨
          0 < fkIsingSquareFullFaceGhostMultiplicity n b) ∧
        (fkIsingSquareFullFaceGraph n).Reachable c b
  suffices ∀ k, P k by
    intro c
    exact this c.2.1 c rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro c hck
      by_cases hk : k = 0
      · have hc0 : c.2.1 = 0 := hck.trans hk
        refine ⟨c, Or.inl ?_, SimpleGraph.Reachable.refl c⟩
        exact Or.inl hc0
      · let q : FKIsingSquareFullFaceNode n :=
          (c.1, ⟨c.2.1 - 1, by omega⟩)
        have hqk : q.2.1 < k := by simp [q]; omega
        obtain ⟨b, hb, hqb⟩ := ih q.2.1 hqk q rfl
        refine ⟨b, hb, ?_⟩
        have hcq : (fkIsingSquareFullFaceGraph n).Adj c q := by
          apply Or.inl
          exact ⟨rfl, Or.inr (by simp [q]; omega)⟩
        exact hcq.reachable.trans hqb


theorem fkIsingSquareFullVertex_zero_le_of_modifiedSuperharmonic
    (n : Nat) (H : FKIsingSquareFullVertexNode n → Real)
    (hmodified : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) H x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - H x) ≤ 0)
    (hfixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ H x) :
    ∀ x, 0 ≤ H x := by
  exact isingFermionicGhost_const_le_superharmonic_boundaryWith
    (fkIsingSquareFullVertexGraph n)
    (fkIsingSquareFullVertexGhostMultiplicity n)
    (fkIsingSquareFullVertexFixedBoundary n) H 1 0
    (fkIsingSquareFullVertex_reaches_fixed_or_ghost n)
    hmodified (by norm_num) hfixed


theorem fkIsingSquareFullFace_le_one_of_modifiedSubharmonic
    (n : Nat) (H : FKIsingSquareFullFaceNode n → Real)
    (hmodified : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - H c))
    (hfixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c → H c ≤ 1) :
    ∀ c, H c ≤ 1 := by
  exact isingFermionicGhost_subharmonic_le_const_boundaryWith
    (fkIsingSquareFullFaceGraph n)
    (fkIsingSquareFullFaceGhostMultiplicity n)
    (fkIsingSquareFullFaceFixedBoundary n) H 0 1
    (fkIsingSquareFullFace_reaches_fixed_or_ghost n)
    hmodified (by norm_num) hfixed


end
end StatMech.Universality
