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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part3


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem fullSquareScaledEmbedding_incidenceDistance
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (mesh : Nat → Real) (hmesh : ∀ k, 0 ≤ mesh k)
    (k : Nat)
    (e : FKIsingSquareInteriorRadialIncidence (N k) (hN k)) :
    dist
        (fullSquareScaledFaceEmbedding (N k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))
        (fullSquareScaledVertexEmbedding (N k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) ≤ mesh k :=
  (fullSquareScaledEmbeddingCompatibility N mesh hmesh).incidenceDistance
    (hN := hN) k e

theorem vertexSampled_boundaryConsistencyError_le
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) (bound : Real) (hbound : 0 ≤ bound)
    (hfixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x →
      |0 - (Phi (embedding x)).im| ≤ bound) :
    vertexBoundaryConsistencyError n hn
      (vertexSampledImaginaryTarget n embedding Phi) ≤ bound := by
  apply isingFiniteWeightedBoundaryError_le
    (vertexDirichletBoundary n) (vertexGhostPrimitive n hn)
    (vertexSampledImaginaryTarget n embedding Phi) bound hbound
  intro x hx
  cases x with
  | none => simpa [vertexGhostPrimitive, vertexSampledImaginaryTarget,
      isingFiniteGhostExtension] using hbound
  | some x =>
      change fkIsingSquareFullVertexFixedBoundary n x at hx
      simpa [vertexGhostPrimitive, vertexSampledImaginaryTarget,
        isingFiniteGhostExtension, vertex_fixedBoundary_eq_zero n hn x hx]
        using hfixed x hx

theorem faceSampled_boundaryConsistencyError_le
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) (bound : Real) (hbound : 0 ≤ bound)
    (hfixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c →
      |1 - (Phi (embedding c)).im| ≤ bound) :
    faceBoundaryConsistencyError n hn
      (faceSampledImaginaryTarget n embedding Phi) ≤ bound := by
  apply isingFiniteWeightedBoundaryError_le
    (faceDirichletBoundary n) (faceGhostPrimitive n hn)
    (faceSampledImaginaryTarget n embedding Phi) bound hbound
  intro c hc
  cases c with
  | none => simpa [faceGhostPrimitive, faceSampledImaginaryTarget,
      isingFiniteGhostExtension] using hbound
  | some c =>
      change fkIsingSquareFullFaceFixedBoundary n c at hc
      simpa [faceGhostPrimitive, faceSampledImaginaryTarget,
        isingFiniteGhostExtension, face_fixedBoundary_eq_one n hn c hc]
        using hfixed c hc

theorem vertexSampled_boundaryConsistencyError_eq_zero
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex)
    (hfixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x →
      (Phi (embedding x)).im = 0) :
    vertexBoundaryConsistencyError n hn
      (vertexSampledImaginaryTarget n embedding Phi) = 0 := by
  apply le_antisymm
  · apply vertexSampled_boundaryConsistencyError_le
      n hn embedding Phi 0 (le_refl 0)
    intro x hx
    simp [hfixed x hx]
  · exact isingFiniteWeightedBoundaryError_nonneg
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn)
      (vertexSampledImaginaryTarget n embedding Phi)

theorem faceSampled_boundaryConsistencyError_eq_zero
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex)
    (hfixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c →
      (Phi (embedding c)).im = 1) :
    faceBoundaryConsistencyError n hn
      (faceSampledImaginaryTarget n embedding Phi) = 0 := by
  apply le_antisymm
  · apply faceSampled_boundaryConsistencyError_le
      n hn embedding Phi 0 (le_refl 0)
    intro c hc
    simp [hfixed c hc]
  · exact isingFiniteWeightedBoundaryError_nonneg
      (faceDirichletBoundary n) (faceGhostPrimitive n hn)
      (faceSampledImaginaryTarget n embedding Phi)

theorem vertexSampled_targetResidual_le
    (n : Nat)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) (bound : Real) (hbound : 0 ≤ bound)
    (hrobin : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ (Phi (embedding y)).im) x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (Phi (embedding x)).im)| ≤ bound) :
    vertexTargetResidual n
      (vertexSampledImaginaryTarget n embedding Phi) ≤ bound := by
  apply isingFiniteWeightedTargetResidual_le
    (vertexGhostConductance n) (vertexDirichletBoundary n)
    (vertexSampledImaginaryTarget n embedding Phi) bound hbound
  intro x hx
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      change ¬ fkIsingSquareFullVertexFixedBoundary n x at hx
      have h := hrobin x hx
      have htarget : vertexSampledImaginaryTarget n embedding Phi =
          isingFiniteGhostExtension 1
            (fun y ↦ (Phi (embedding y)).im) := by
        funext z
        cases z <;> rfl
      rw [htarget]
      unfold vertexGhostConductance
      rw [isingFiniteGhostLaplacian_some]
      exact h

theorem faceSampled_targetResidual_le
    (n : Nat)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) (bound : Real) (hbound : 0 ≤ bound)
    (hrobin : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ (Phi (embedding d)).im) c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (0 - (Phi (embedding c)).im)| ≤ bound) :
    faceTargetResidual n
      (faceSampledImaginaryTarget n embedding Phi) ≤ bound := by
  apply isingFiniteWeightedTargetResidual_le
    (faceGhostConductance n) (faceDirichletBoundary n)
    (faceSampledImaginaryTarget n embedding Phi) bound hbound
  intro c hc
  cases c with
  | none => exact False.elim (hc trivial)
  | some c =>
      change ¬ fkIsingSquareFullFaceFixedBoundary n c at hc
      have h := hrobin c hc
      have htarget : faceSampledImaginaryTarget n embedding Phi =
          isingFiniteGhostExtension 0
            (fun d ↦ (Phi (embedding d)).im) := by
        funext z
        cases z <;> rfl
      rw [htarget]
      unfold faceGhostConductance
      rw [isingFiniteGhostLaplacian_some]
      exact h

theorem fullVertexGhostMultiplicity_le_three
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    fkIsingSquareFullVertexGhostMultiplicity n x ≤ 3 := by
  unfold fkIsingSquareFullVertexGhostMultiplicity
  split_ifs <;> omega

theorem fullFaceGhostMultiplicity_le_one
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareFullFaceGhostMultiplicity n c ≤ 1 := by
  unfold fkIsingSquareFullFaceGhostMultiplicity
  split_ifs <;> omega

theorem vertexGhostRate_le_threeCoefficient
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x ≤
      3 * isingFermionicGhostCoefficient := by
  unfold isingFermionicGhostRate
  have h : (fkIsingSquareFullVertexGhostMultiplicity n x : Real) ≤ 3 := by
    exact_mod_cast fullVertexGhostMultiplicity_le_three n x
  nlinarith [isingFermionicGhostCoefficient_pos.le]

theorem faceGhostRate_le_coefficient
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    isingFermionicGhostRate
        (fkIsingSquareFullFaceGhostMultiplicity n) c ≤
      isingFermionicGhostCoefficient := by
  unfold isingFermionicGhostRate
  have h : (fkIsingSquareFullFaceGhostMultiplicity n c : Real) ≤ 1 := by
    exact_mod_cast fullFaceGhostMultiplicity_le_one n c
  nlinarith [isingFermionicGhostCoefficient_pos.le]


theorem vertexSampled_robinResidual_le_of_laplacian_and_trace
    (n : Nat)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound traceBound : Real)
    (htrace_nonneg : 0 ≤ traceBound)
    (hlaplacian : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y ↦ (Phi (embedding y)).im) x| ≤ laplacianBound)
    (htrace : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
      0 < fkIsingSquareFullVertexGhostMultiplicity n x →
        |1 - (Phi (embedding x)).im| ≤ traceBound) :
    ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ (Phi (embedding y)).im) x +
        isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (Phi (embedding x)).im)| ≤
        laplacianBound +
          (3 * isingFermionicGhostCoefficient) * traceBound := by
  intro x hx
  let rate := isingFermionicGhostRate
    (fkIsingSquareFullVertexGhostMultiplicity n) x
  let jump := 1 - (Phi (embedding x)).im
  calc
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ (Phi (embedding y)).im) x + rate * jump| ≤
        |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ (Phi (embedding y)).im) x| + |rate * jump| :=
      abs_add_le _ _
    _ = |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ (Phi (embedding y)).im) x| + rate * |jump| := by
      have hrate : 0 ≤ rate := isingFermionicGhostRate_nonneg _ x
      rw [abs_mul, abs_of_nonneg hrate]
    _ ≤ laplacianBound +
        (3 * isingFermionicGhostCoefficient) * traceBound := by
      apply add_le_add (hlaplacian x hx)
      by_cases hpositive :
          0 < fkIsingSquareFullVertexGhostMultiplicity n x
      · exact mul_le_mul (vertexGhostRate_le_threeCoefficient n x)
          (htrace x hx hpositive) (abs_nonneg _)
          (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)
      · have hzero : fkIsingSquareFullVertexGhostMultiplicity n x = 0 :=
          Nat.eq_zero_of_not_pos hpositive
        simp [rate, isingFermionicGhostRate, hzero,
          mul_nonneg
            (mul_nonneg (by norm_num : (0 : Real) ≤ 3)
              isingFermionicGhostCoefficient_pos.le)
            htrace_nonneg]


theorem faceSampled_robinResidual_le_of_laplacian_and_trace
    (n : Nat)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound traceBound : Real)
    (htrace_nonneg : 0 ≤ traceBound)
    (hlaplacian : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d ↦ (Phi (embedding d)).im) c| ≤ laplacianBound)
    (htrace : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
      0 < fkIsingSquareFullFaceGhostMultiplicity n c →
        |0 - (Phi (embedding c)).im| ≤ traceBound) :
    ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ (Phi (embedding d)).im) c +
        isingFermionicGhostRate
            (fkIsingSquareFullFaceGhostMultiplicity n) c *
          (0 - (Phi (embedding c)).im)| ≤
        laplacianBound + isingFermionicGhostCoefficient * traceBound := by
  intro c hc
  let rate := isingFermionicGhostRate
    (fkIsingSquareFullFaceGhostMultiplicity n) c
  let jump := 0 - (Phi (embedding c)).im
  calc
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ (Phi (embedding d)).im) c + rate * jump| ≤
        |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ (Phi (embedding d)).im) c| + |rate * jump| :=
      abs_add_le _ _
    _ = |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ (Phi (embedding d)).im) c| + rate * |jump| := by
      have hrate : 0 ≤ rate := isingFermionicGhostRate_nonneg _ c
      rw [abs_mul, abs_of_nonneg hrate]
    _ ≤ laplacianBound + isingFermionicGhostCoefficient * traceBound := by
      apply add_le_add (hlaplacian c hc)
      by_cases hpositive : 0 < fkIsingSquareFullFaceGhostMultiplicity n c
      · exact mul_le_mul (faceGhostRate_le_coefficient n c)
          (htrace c hc hpositive) (abs_nonneg _)
          isingFermionicGhostCoefficient_pos.le
      · have hzero : fkIsingSquareFullFaceGhostMultiplicity n c = 0 :=
          Nat.eq_zero_of_not_pos hpositive
        simp [rate, isingFermionicGhostRate, hzero,
          mul_nonneg isingFermionicGhostCoefficient_pos.le htrace_nonneg]

theorem vertexSampled_targetResidual_le_of_laplacian_and_trace
    (n : Nat)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound traceBound : Real)
    (hlaplacian_nonneg : 0 ≤ laplacianBound)
    (htrace_nonneg : 0 ≤ traceBound)
    (hlaplacian : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y ↦ (Phi (embedding y)).im) x| ≤ laplacianBound)
    (htrace : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
      0 < fkIsingSquareFullVertexGhostMultiplicity n x →
        |1 - (Phi (embedding x)).im| ≤ traceBound) :
    vertexTargetResidual n
        (vertexSampledImaginaryTarget n embedding Phi) ≤
      laplacianBound +
        (3 * isingFermionicGhostCoefficient) * traceBound := by
  apply vertexSampled_targetResidual_le n embedding Phi
  · exact add_nonneg hlaplacian_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)
        htrace_nonneg)
  · exact vertexSampled_robinResidual_le_of_laplacian_and_trace
      n embedding Phi laplacianBound traceBound htrace_nonneg
      hlaplacian htrace

theorem faceSampled_targetResidual_le_of_laplacian_and_trace
    (n : Nat)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound traceBound : Real)
    (hlaplacian_nonneg : 0 ≤ laplacianBound)
    (htrace_nonneg : 0 ≤ traceBound)
    (hlaplacian : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d ↦ (Phi (embedding d)).im) c| ≤ laplacianBound)
    (htrace : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
      0 < fkIsingSquareFullFaceGhostMultiplicity n c →
        |0 - (Phi (embedding c)).im| ≤ traceBound) :
    faceTargetResidual n
        (faceSampledImaginaryTarget n embedding Phi) ≤
      laplacianBound + isingFermionicGhostCoefficient * traceBound := by
  apply faceSampled_targetResidual_le n embedding Phi
  · exact add_nonneg hlaplacian_nonneg
      (mul_nonneg isingFermionicGhostCoefficient_pos.le htrace_nonneg)
  · exact faceSampled_robinResidual_le_of_laplacian_and_trace
      n embedding Phi laplacianBound traceBound htrace_nonneg
      hlaplacian htrace

theorem vertexSampled_targetResidual_le_of_exact_free_trace
    (n : Nat)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound : Real)
    (hlaplacian_nonneg : 0 ≤ laplacianBound)
    (hlaplacian : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y ↦ (Phi (embedding y)).im) x| ≤ laplacianBound)
    (hfree : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
      0 < fkIsingSquareFullVertexGhostMultiplicity n x →
        (Phi (embedding x)).im = 1) :
    vertexTargetResidual n
        (vertexSampledImaginaryTarget n embedding Phi) ≤ laplacianBound := by
  simpa using vertexSampled_targetResidual_le_of_laplacian_and_trace
    n embedding Phi laplacianBound 0 hlaplacian_nonneg (le_refl 0)
    hlaplacian (fun x hfixed hx ↦ by simp [hfree x hfixed hx])

theorem faceSampled_targetResidual_le_of_exact_free_trace
    (n : Nat)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound : Real)
    (hlaplacian_nonneg : 0 ≤ laplacianBound)
    (hlaplacian : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d ↦ (Phi (embedding d)).im) c| ≤ laplacianBound)
    (hfree : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
      0 < fkIsingSquareFullFaceGhostMultiplicity n c →
        (Phi (embedding c)).im = 0) :
    faceTargetResidual n
        (faceSampledImaginaryTarget n embedding Phi) ≤ laplacianBound := by
  simpa using faceSampled_targetResidual_le_of_laplacian_and_trace
    n embedding Phi laplacianBound 0 hlaplacian_nonneg (le_refl 0)
    hlaplacian (fun c hfixed hc ↦ by simp [hfree c hfixed hc])

theorem fullVertex_neighbor_card_le_four
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    Nat.card ↑((fkIsingSquareFullVertexGraph n).neighborSet x) ≤ 4 := by
  classical
  let f : (fkIsingSquareFullVertexGraph n).neighborSet x →
      (hypercubicLattice 2).neighborSet x.1 := fun y ↦ ⟨y.1.1, y.2⟩
  have hf : Function.Injective f := by
    intro y z hyz
    dsimp [f] at hyz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun w : (hypercubicLattice 2).neighborSet x.1 ↦ w.1) hyz
  calc
    Nat.card ((fkIsingSquareFullVertexGraph n).neighborSet x) ≤
        Nat.card ((hypercubicLattice 2).neighborSet x.1) :=
      Nat.card_le_card_of_injective f hf
    _ = (hypercubicLattice 2).degree x.1 :=
      (Nat.card_eq_fintype_card).trans
        (SimpleGraph.card_neighborSet_eq_degree _ _)
    _ = 4 := by simpa using degree_eq 2 x.1

theorem vertexQuadraticBarrier_laplacian_le
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fkIsingSquareBoxQuadraticBarrier n) x ≤ 2 * (n : Real) ^ 2 := by
  classical
  have hcardNat :
      ((fkIsingSquareFullVertexGraph n).neighborFinset x).card ≤ 4 := by
    have hncard : Nat.card
        ↑((fkIsingSquareFullVertexGraph n).neighborSet x) =
        (fkIsingSquareFullVertexGraph n).degree x :=
      (Nat.card_eq_fintype_card).trans
        (SimpleGraph.card_neighborSet_eq_degree _ _)
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    rw [← hncard]
    exact fullVertex_neighbor_card_le_four n x
  have hcard :
      (((fkIsingSquareFullVertexGraph n).neighborFinset x).card : Real) ≤ 4 := by
    exact_mod_cast hcardNat
  unfold isingFiniteGraphLaplacian
  calc
    (∑ y ∈ (fkIsingSquareFullVertexGraph n).neighborFinset x,
        (fkIsingSquareBoxQuadraticBarrier n y -
          fkIsingSquareBoxQuadraticBarrier n x)) ≤
        ∑ _y ∈ (fkIsingSquareFullVertexGraph n).neighborFinset x,
          ((n : Real) ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro y hy
      have hyBound := fkIsingSquareBoxQuadraticBarrier_le n y
      have hxNonneg := fkIsingSquareBoxQuadraticBarrier_nonneg n x
      linarith
    _ = (((fkIsingSquareFullVertexGraph n).neighborFinset x).card : Real) *
        ((n : Real) ^ 2 / 2) := by simp
    _ ≤ 4 * ((n : Real) ^ 2 / 2) := by gcongr
    _ = 2 * (n : Real) ^ 2 := by ring

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
