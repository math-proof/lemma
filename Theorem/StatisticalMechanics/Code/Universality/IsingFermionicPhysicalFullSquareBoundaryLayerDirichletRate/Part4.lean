/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part4


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexBarrierOffset_nonneg (n : Nat) :
    0 ≤ vertexBarrierOffset n := by
  unfold vertexBarrierOffset
  exact div_nonneg (by positivity) isingFermionicGhostCoefficient_pos.le

theorem vertexExplicitPoissonBarrier_nonneg (n : Nat) :
    ∀ x, 0 ≤ vertexExplicitPoissonBarrier n x := by
  intro x
  cases x with
  | none => simp [vertexExplicitPoissonBarrier]
  | some x =>
      simp only [vertexExplicitPoissonBarrier]
      exact add_nonneg (fkIsingSquareBoxQuadraticBarrier_nonneg n x)
        (vertexBarrierOffset_nonneg n)

theorem vertexExplicitPoissonBarrier_le_bound (n : Nat) :
    ∀ x, vertexExplicitPoissonBarrier n x ≤
      vertexExplicitPoissonBarrierBound n := by
  intro x
  cases x with
  | none =>
      simp only [vertexExplicitPoissonBarrier]
      exact add_nonneg (by positivity) (vertexBarrierOffset_nonneg n)
  | some x =>
      simpa [vertexExplicitPoissonBarrier,
        vertexExplicitPoissonBarrierBound, add_comm] using
          add_le_add_right (fkIsingSquareBoxQuadraticBarrier_le n x)
            (vertexBarrierOffset n)

theorem vertexExplicitPoissonBarrier_laplacian
    (n : Nat) (hn : 0 < n)
    (x : Option (FKIsingSquareFullVertexNode n))
    (hx : ¬ vertexDirichletBoundary n x) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexExplicitPoissonBarrier n) x ≤ -1 := by
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      change ¬ fkIsingSquareFullVertexFixedBoundary n x at hx
      let Q := fkIsingSquareBoxQuadraticBarrier n
      let C := vertexBarrierOffset n
      let f : FKIsingSquareFullVertexNode n → Real := fun y ↦ Q y + C
      have hbarrier : vertexExplicitPoissonBarrier n =
          isingFiniteGhostExtension 0 f := by
        funext z
        cases z <;> rfl
      change isingFiniteWeightedLaplacian
        (isingFiniteGhostConductance (fkIsingSquareFullVertexGraph n)
          (isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n)))
        (vertexExplicitPoissonBarrier n) (some x) ≤ -1
      rw [hbarrier, isingFiniteGhostLaplacian_some]
      by_cases hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity n x
      · have hgraph := vertexQuadraticBarrier_laplacian_le n x
        have hgraphf : isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph n) f x =
            isingFiniteGraphLaplacian
              (fkIsingSquareFullVertexGraph n) Q x := by
          exact isingFiniteGraphLaplacian_add_const
            (fkIsingSquareFullVertexGraph n) Q C x
        have hQ : 0 ≤ Q x := fkIsingSquareBoxQuadraticBarrier_nonneg n x
        have hcoef : 0 < isingFermionicGhostCoefficient :=
          isingFermionicGhostCoefficient_pos
        have hm : (1 : Real) ≤
            (fkIsingSquareFullVertexGhostMultiplicity n x : Real) := by
          exact_mod_cast hghost
        have hrateC : 2 * (n : Real) ^ 2 + 1 ≤
            isingFermionicGhostRate
                (fkIsingSquareFullVertexGhostMultiplicity n) x * C := by
          unfold isingFermionicGhostRate C vertexBarrierOffset
          field_simp
          nlinarith
        have hrate : 0 ≤ isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x :=
          isingFermionicGhostRate_nonneg
            (fkIsingSquareFullVertexGhostMultiplicity n) x
        rw [hgraphf]
        dsimp only [f]
        nlinarith
      · have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 0 :=
          Nat.eq_zero_of_not_pos hghost
        have hinterior : ¬ fkIsingSquareBoxBoundary n x := by
          intro hboundary
          rcases fkIsingSquareFullVertex_boundary_fixed_or_ghost
              n x hboundary with hfixed | hpos
          · exact hx hfixed
          · exact hghost hpos
        have hQlap := fkIsingSquareBoxQuadraticBarrier_laplacian
          n x hinterior
        have hQlap' : isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph n) Q x = -1 := by
          simpa [fkIsingSquareFullVertexGraph, Q] using hQlap
        rw [show isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph n) f x =
            isingFiniteGraphLaplacian
              (fkIsingSquareFullVertexGraph n) Q x by
          exact isingFiniteGraphLaplacian_add_const
            (fkIsingSquareFullVertexGraph n) Q C x]
        simp [isingFermionicGhostRate, hmult, hQlap']

theorem vertexPoissonBarrier_le_explicit
    (n : Nat) (hn : 0 < n) : ∀ x,
    isingFiniteWeightedPoissonBarrier
        (vertexGhostGraph n) (vertexGhostConductance n)
        (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
        (vertexGhostConductance_pos_of_adj n)
        (vertexGhost_reaches_boundary n) x ≤
      vertexExplicitPoissonBarrier n x := by
  apply isingFiniteWeighted_laplacian_comparison
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n)
    (isingFiniteWeightedPoissonBarrier
      (vertexGhostGraph n) (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
      (vertexGhostConductance_pos_of_adj n)
      (vertexGhost_reaches_boundary n))
    (vertexExplicitPoissonBarrier n)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)
  · intro x hx
    rw [isingFiniteWeightedPoissonBarrier_boundary
      (vertexGhostGraph n) (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
      (vertexGhostConductance_pos_of_adj n)
      (vertexGhost_reaches_boundary n) x hx]
    exact vertexExplicitPoissonBarrier_nonneg n x
  · intro x hx
    rw [isingFiniteWeightedPoissonBarrier_laplacian
      (vertexGhostGraph n) (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
      (vertexGhostConductance_pos_of_adj n)
      (vertexGhost_reaches_boundary n) x hx]
    exact vertexExplicitPoissonBarrier_laplacian n hn x hx

theorem vertexPoissonBarrierBound_le_explicit
    (n : Nat) (hn : 0 < n) :
    vertexPoissonBarrierBound n ≤ vertexExplicitPoissonBarrierBound n := by
  unfold vertexPoissonBarrierBound isingFiniteWeightedPoissonBarrierBound
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
  exact (vertexPoissonBarrier_le_explicit n hn x).trans
    (vertexExplicitPoissonBarrier_le_bound n x)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
