/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryLayerConsistency.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCalibratedRobinConsistency
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility


namespace StatMech.Universality

open Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant_continuous
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k) :
    Continuous
      (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm) :=
  fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_continuous _ _ _ _ _ _


theorem fkIsingExpandingBoundarySquareRadial_embedding_dist_lt
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k)
    (i j : Fin m) (s : FKIsingMedialSide) :
    dist
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding
          k (fkIsingExpandingBoundarySquareRadialDart k m hm i j s))
        (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1) <
      fkIsingExpandingSquareScale k / 10 := by
  change dist
      (fkIsingSquareWiredPerturbedCarrierPosition
        (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
        (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
        (.dart (fkIsingSquareRadialPatchEdge
          (fkIsingExpandingSquareSide k) m hm i j, s)))
      (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1) < _
  rw [fkIsingExpandingBoundarySquareRadialSamplePosition,
    isingRadialGridPosition_eq_scaledCarrierPosition]
  exact fkIsingSquareWiredPerturbedCarrierPosition_dist_lt
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
    (.dart (fkIsingSquareRadialPatchEdge
      (fkIsingExpandingSquareSide k) m hm i j, s))


theorem fkIsingExpandingBoundarySquareRadial_normalizedObservable
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k)
    (i j : Fin m) (s : FKIsingMedialSide) :
    @FKIsingDobrushinDomain.normalizedFermionicObservable
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)
        (fkIsingExpandingBoundarySquareRadialDart k m hm i j s) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)
        (.dart (fkIsingSquareRadialPatchEdge
          (fkIsingExpandingSquareSide k) m hm i j, s)) := by
  rfl


theorem fkIsingExpandingBoundarySquareRadial_projection_sample
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k)
    (i j : Fin m) (s : FKIsingMedialSide) :
    isingProj
        (fkIsingSquareWiredDirectedTangent
          (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
          (fkIsingExpandingBoundarySquareRadialDart k m hm i j s))
        (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm
          (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1)) =
      @FKIsingDobrushinDomain.normalizedFermionicObservable
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)
        (fkIsingExpandingBoundarySquareRadialDart k m hm i j s) := by
  rw [fkIsingExpandingBoundarySquareRadial_normalizedObservable]
  exact fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_projection
    (fkIsingExpandingSquareSide k) m (fkIsingExpandingSquareSide_pos k) hm
    (fkIsingExpandingSquareScale k)
    (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)
    (fkIsingExpandingSquareScale_pos k) i j s


theorem fkIsingExpandingBoundarySquareRadial_projection_embedding_dist_le
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k)
    (i j : Fin m) (s : FKIsingMedialSide) (C alpha : NNReal)
    (hholder : HolderWith C alpha
      (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm)) :
    dist
        (isingProj
          (fkIsingSquareWiredDirectedTangent
            (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
            (fkIsingExpandingBoundarySquareRadialDart k m hm i j s))
          (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm
            (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k
              (fkIsingExpandingBoundarySquareRadialDart k m hm i j s))))
        (@FKIsingDobrushinDomain.normalizedFermionicObservable
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)
          (fkIsingExpandingBoundarySquareRadialDart k m hm i j s)) ≤
      C *
        dist
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding
            k (fkIsingExpandingBoundarySquareRadialDart k m hm i j s))
          (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1) ^
            (alpha : Real) := by
  apply isingProj_dist_le_of_nearby_holder
  · rw [Complex.normSq_eq_norm_sq]
    simp [fkIsingSquareWiredDirectedTangent, Complex.norm_exp]
  · exact hholder
  · exact fkIsingExpandingBoundarySquareRadial_projection_sample
      k m hm i j s

namespace FKIsingSquareBoundaryLayerCoordinateOneForm


theorem fullSquareScaledVertexEmbedding_dist_le_two_abs
    (n : Nat) (scale : Real) (x y : FKIsingSquareFullVertexNode n)
    (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
    dist (fullSquareScaledVertexEmbedding n scale y)
        (fullSquareScaledVertexEmbedding n scale x) ≤ 2 * |scale| := by
  have hunit : unitWt (y.1 - x.1) = 1 := by
    exact (adj_iff_unitWt_sub y.1 x.1).1 hxy.symm
  have hcases :
      (y.1 0 = x.1 0 + 1 ∧ y.1 1 = x.1 1) ∨
      (y.1 0 + 1 = x.1 0 ∧ y.1 1 = x.1 1) ∨
      (y.1 0 = x.1 0 ∧ y.1 1 = x.1 1 + 1) ∨
      (y.1 0 = x.1 0 ∧ y.1 1 + 1 = x.1 1) := by
    unfold unitWt at hunit
    simp only [Fin.sum_univ_two, Pi.sub_apply] at hunit
    omega
  rw [dist_eq_norm]
  calc
    ‖fullSquareScaledVertexEmbedding n scale y -
        fullSquareScaledVertexEmbedding n scale x‖ ≤
      |(fullSquareScaledVertexEmbedding n scale y -
        fullSquareScaledVertexEmbedding n scale x).re| +
      |(fullSquareScaledVertexEmbedding n scale y -
        fullSquareScaledVertexEmbedding n scale x).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 2 * |scale| := by
      rcases hcases with ⟨h0, h1⟩ | ⟨h0, h1⟩ |
          ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have h0R : (y.1 0 : Real) = (x.1 0 : Real) + 1 := by
          exact_mod_cast h0
        have h1R : (y.1 1 : Real) = (x.1 1 : Real) := by
          exact_mod_cast h1
        simp [fullSquareScaledVertexEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullVertexCoordinate,
          fkIsingSquareWiredIntPoint, h0R, h1R, abs_mul]
        ring
      · have h0R : (y.1 0 : Real) + 1 = (x.1 0 : Real) := by
          exact_mod_cast h0
        have h1R : (y.1 1 : Real) = (x.1 1 : Real) := by
          exact_mod_cast h1
        have hy0 : (y.1 0 : Real) = (x.1 0 : Real) - 1 := by
          linarith
        simp [fullSquareScaledVertexEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullVertexCoordinate,
          fkIsingSquareWiredIntPoint, hy0, h1R, abs_mul]
        ring_nf
        rw [abs_neg]
      · have h0R : (y.1 0 : Real) = (x.1 0 : Real) := by
          exact_mod_cast h0
        have h1R : (y.1 1 : Real) = (x.1 1 : Real) + 1 := by
          exact_mod_cast h1
        simp [fullSquareScaledVertexEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullVertexCoordinate,
          fkIsingSquareWiredIntPoint, h0R, h1R, abs_mul]
        ring_nf
        rw [abs_neg]
        ring
      · have h0R : (y.1 0 : Real) = (x.1 0 : Real) := by
          exact_mod_cast h0
        have h1R : (y.1 1 : Real) + 1 = (x.1 1 : Real) := by
          exact_mod_cast h1
        have hy1 : (y.1 1 : Real) = (x.1 1 : Real) - 1 := by
          linarith
        simp [fullSquareScaledVertexEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullVertexCoordinate,
          fkIsingSquareWiredIntPoint, h0R, hy1, abs_mul]
        ring_nf
        rw [abs_neg]
        ring


theorem fullSquareScaledFaceEmbedding_dist_le_two_abs
    (n : Nat) (scale : Real) (c d : FKIsingSquareFullFaceNode n)
    (hcd : (fkIsingSquareFullFaceGraph n).Adj c d) :
    dist (fullSquareScaledFaceEmbedding n scale d)
        (fullSquareScaledFaceEmbedding n scale c) ≤ 2 * |scale| := by
  rw [dist_eq_norm]
  calc
    ‖fullSquareScaledFaceEmbedding n scale d -
        fullSquareScaledFaceEmbedding n scale c‖ ≤
      |(fullSquareScaledFaceEmbedding n scale d -
        fullSquareScaledFaceEmbedding n scale c).re| +
      |(fullSquareScaledFaceEmbedding n scale d -
        fullSquareScaledFaceEmbedding n scale c).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 2 * |scale| := by
      rcases hcd with ⟨hcol, hup | hdown⟩ | ⟨hrow, hright | hleft⟩
      · have h0 : c.1.1 = d.1.1 := congrArg Fin.val hcol
        have h1 : (c.2.1 : Real) + 1 = (d.2.1 : Real) := by
          exact_mod_cast hup
        have hd0 : (d.1.1 : Real) = (c.1.1 : Real) := by
          exact_mod_cast h0.symm
        have hd1 : (d.2.1 : Real) = (c.2.1 : Real) + 1 := by
          linarith
        simp [fullSquareScaledFaceEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
          fkIsingSquareWiredIntPoint, hd0, hd1, abs_mul]
        ring_nf
        rw [abs_neg]
        ring
      · have h0 : c.1.1 = d.1.1 := congrArg Fin.val hcol
        have h1 : (d.2.1 : Real) + 1 = (c.2.1 : Real) := by
          exact_mod_cast hdown
        have hd0 : (d.1.1 : Real) = (c.1.1 : Real) := by
          exact_mod_cast h0.symm
        have hd1 : (d.2.1 : Real) = (c.2.1 : Real) - 1 := by
          linarith
        simp [fullSquareScaledFaceEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
          fkIsingSquareWiredIntPoint, hd0, hd1, abs_mul]
        ring_nf
        rw [abs_neg]
        ring
      · have h0 : c.2.1 = d.2.1 := congrArg Fin.val hrow
        have h1 : (c.1.1 : Real) + 1 = (d.1.1 : Real) := by
          exact_mod_cast hright
        have hd0 : (d.2.1 : Real) = (c.2.1 : Real) := by
          exact_mod_cast h0.symm
        have hd1 : (d.1.1 : Real) = (c.1.1 : Real) + 1 := by
          linarith
        simp [fullSquareScaledFaceEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
          fkIsingSquareWiredIntPoint, hd0, hd1, abs_mul]
        ring_nf
      · have h0 : c.2.1 = d.2.1 := congrArg Fin.val hrow
        have h1 : (d.1.1 : Real) + 1 = (c.1.1 : Real) := by
          exact_mod_cast hleft
        have hd0 : (d.2.1 : Real) = (c.2.1 : Real) := by
          exact_mod_cast h0.symm
        have hd1 : (d.1.1 : Real) = (c.1.1 : Real) - 1 := by
          linarith
        simp [fullSquareScaledFaceEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
          fkIsingSquareWiredIntPoint, hd0, hd1, abs_mul]
        ring_nf
        rw [abs_neg]


theorem fullFace_neighbor_card_le_four
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    Nat.card ↑((fkIsingSquareFullFaceGraph n).neighborSet c) ≤ 4 := by
  classical
  let center : Site 2 := ![(c.1.1 : Int), (c.2.1 : Int)]
  let f : (fkIsingSquareFullFaceGraph n).neighborSet c →
      (hypercubicLattice 2).neighborSet center := fun d ↦
    ⟨![(d.1.1.1 : Int), (d.1.2.1 : Int)], by
      change (hypercubicLattice 2).Adj center
        ![(d.1.1.1 : Int), (d.1.2.1 : Int)]
      rw [adj_iff_unitWt_sub]
      rcases d.2 with ⟨hcol, hup | hdown⟩ | ⟨hrow, hright | hleft⟩
      all_goals simp [unitWt, center] at *
      all_goals omega⟩
  have hf : Function.Injective f := by
    intro d e hde
    have h0 := congrArg (fun z : Site 2 ↦ z 0) (congrArg Subtype.val hde)
    have h1 := congrArg (fun z : Site 2 ↦ z 1) (congrArg Subtype.val hde)
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · simpa [f] using h0
    · simpa [f] using h1
  calc
    Nat.card ((fkIsingSquareFullFaceGraph n).neighborSet c) ≤
        Nat.card ((hypercubicLattice 2).neighborSet center) :=
      Nat.card_le_card_of_injective f hf
    _ = (hypercubicLattice 2).degree center :=
      (Nat.card_eq_fintype_card).trans
        (SimpleGraph.card_neighborSet_eq_degree _ _)
    _ = 4 := by simpa using degree_eq 2 center


theorem isingFiniteGraphLaplacian_abs_le_four_mul
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (f : V → Real) (x : V) (D : Real) (hD : 0 ≤ D)
    (hcard : Nat.card ↑(G.neighborSet x) ≤ 4)
    (hneighbor : ∀ y, G.Adj x y → |f y - f x| ≤ D) :
    |isingFiniteGraphLaplacian G f x| ≤ 4 * D := by
  classical
  have hcardFinset : (G.neighborFinset x).card ≤ 4 := by
    have hncard : Nat.card ↑(G.neighborSet x) = G.degree x :=
      (Nat.card_eq_fintype_card).trans
        (SimpleGraph.card_neighborSet_eq_degree _ _)
    rw [SimpleGraph.card_neighborFinset_eq_degree, ← hncard]
    exact hcard
  unfold isingFiniteGraphLaplacian
  calc
    |∑ y ∈ G.neighborFinset x, (f y - f x)| ≤
        ∑ y ∈ G.neighborFinset x, |f y - f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ G.neighborFinset x, D := by
      apply Finset.sum_le_sum
      intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      exact hneighbor y hy
    _ = ((G.neighborFinset x).card : Real) * D := by simp
    _ ≤ 4 * D := by
      gcongr
      exact_mod_cast hcardFinset


theorem fullSquareScaledVertex_sampledLaplacian_le_lipschitz
    (n : Nat) (scale : Real) (Phi : Complex → Complex)
    (L : NNReal) (hPhi : LipschitzWith L (fun z ↦ (Phi z).im))
    (x : FKIsingSquareFullVertexNode n) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y ↦ (Phi (fullSquareScaledVertexEmbedding n scale y)).im) x| ≤
        8 * (L : Real) * |scale| := by
  have hD : 0 ≤ 2 * (L : Real) * |scale| := by positivity
  calc
    _ ≤ 4 * (2 * (L : Real) * |scale|) := by
      apply isingFiniteGraphLaplacian_abs_le_four_mul
        (fkIsingSquareFullVertexGraph n) _ x _ hD
          (fullVertex_neighbor_card_le_four n x)
      intro y hxy
      rw [← Real.dist_eq]
      exact (hPhi.dist_le_mul _ _).trans (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left
            (fullSquareScaledVertexEmbedding_dist_le_two_abs
              n scale x y hxy) L.2))
    _ = 8 * (L : Real) * |scale| := by ring


theorem fullSquareScaledFace_sampledLaplacian_le_lipschitz
    (n : Nat) (scale : Real) (Phi : Complex → Complex)
    (L : NNReal) (hPhi : LipschitzWith L (fun z ↦ (Phi z).im))
    (c : FKIsingSquareFullFaceNode n) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun d ↦ (Phi (fullSquareScaledFaceEmbedding n scale d)).im) c| ≤
        8 * (L : Real) * |scale| := by
  have hD : 0 ≤ 2 * (L : Real) * |scale| := by positivity
  calc
    _ ≤ 4 * (2 * (L : Real) * |scale|) := by
      apply isingFiniteGraphLaplacian_abs_le_four_mul
        (fkIsingSquareFullFaceGraph n) _ c _ hD
          (fullFace_neighbor_card_le_four n c)
      intro d hcd
      rw [← Real.dist_eq]
      exact (hPhi.dist_le_mul _ _).trans (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left
            (fullSquareScaledFaceEmbedding_dist_le_two_abs
              n scale c d hcd) L.2))
    _ = 8 * (L : Real) * |scale| := by ring


theorem fullSquareVertex_bulk_directions
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (hfixed : ¬ fkIsingSquareFullVertexFixedBoundary n x)
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0) :
    fkIsingSquareDirectionAvailable n x .east ∧
      fkIsingSquareDirectionAvailable n x .north ∧
      fkIsingSquareDirectionAvailable n x .west ∧
      fkIsingSquareDirectionAvailable n x .south := by
  have hx := fkIsingSquareVertex_coordinate_bounds n x 0
  have hy := fkIsingSquareVertex_coordinate_bounds n x 1
  have hwest_ne : x.1 0 ≠ -(n : Int) := by
    simpa [fkIsingSquareFullVertexFixedBoundary, fkIsingSquareWiredArc]
      using hfixed
  have heast_ne : x.1 0 ≠ (n : Int) := by
    intro heast
    have hpos : 0 < fkIsingSquareFullVertexGhostMultiplicity n x :=
      (fkIsingSquareFullVertexGhostMultiplicity_pos_iff n x).2
        (Or.inr (Or.inl heast))
    omega
  have hnorth_ne : x.1 1 ≠ (n : Int) := by
    intro hnorth
    have hpos : 0 < fkIsingSquareFullVertexGhostMultiplicity n x :=
      (fkIsingSquareFullVertexGhostMultiplicity_pos_iff n x).2
        (Or.inr (Or.inr hnorth))
    omega
  have hsouth_ne : x.1 1 ≠ -(n : Int) := by
    intro hsouth
    have hpos : 0 < fkIsingSquareFullVertexGhostMultiplicity n x :=
      (fkIsingSquareFullVertexGhostMultiplicity_pos_iff n x).2
        (Or.inl hsouth)
    omega
  simp only [fkIsingSquareDirectionAvailable]
  omega


theorem fullSquareFace_bulk_coordinates
    (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (hfixed : ¬ fkIsingSquareFullFaceFixedBoundary n c)
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0) :
    c.1.1 + 1 < 2 * n ∧ c.2.1 + 1 < 2 * n ∧
      0 < c.1.1 ∧ 0 < c.2.1 := by
  have hx := c.1.2
  have hy := c.2.2
  have hwest_ne : c.1.1 ≠ 0 := by
    intro hwest
    have hpos : 0 < fkIsingSquareFullFaceGhostMultiplicity n c :=
      (fkIsingSquareFullFaceGhostMultiplicity_pos_iff n c).2 hwest
    omega
  have hsouth_ne : c.2.1 ≠ 0 := by
    intro hsouth
    exact hfixed (Or.inl hsouth)
  have heast_ne : c.1.1 + 1 ≠ 2 * n := by
    intro heast
    exact hfixed (Or.inr (Or.inl heast))
  have hnorth_ne : c.2.1 + 1 ≠ 2 * n := by
    intro hnorth
    exact hfixed (Or.inr (Or.inr hnorth))
  omega


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
