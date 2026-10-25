/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSpatialResidualComparison.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialShellCardinality.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStripCauchyFourthOrder
open Metric


namespace StatMech.Universality

open Metric

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem unitStripCenteredBallFourthOrderResidualBound_eq
    (h d : Real) :
    unitStripCenteredBallFourthOrderResidualBound h d =
      8192 * |h| ^ 4 / d ^ 4 := by
  unfold unitStripCenteredBallFourthOrderResidualBound
  change ((4 * (12288 / d ^ 4) + 4 * (12288 / d ^ 4)) *
    |h| ^ 4 / 12) = 8192 * |h| ^ 4 / d ^ 4
  ring


theorem unitStripCenteredBallFourthOrderResidualBound_distanceScale
    (h rho : Real) (hh : h ≠ 0) (hrho : rho ≠ 0) :
    unitStripCenteredBallFourthOrderResidualBound h (|h| * rho) =
      8192 / rho ^ 4 := by
  rw [unitStripCenteredBallFourthOrderResidualBound_eq]
  field_simp [abs_ne_zero.mpr hh, hrho]

theorem verticalOscillationCenteredBallFourthOrderResidualBound_eq
    (C : NNReal) (h d : Real) :
    verticalOscillationCenteredBallFourthOrderResidualBound C h d =
      8192 * (C : Real) * |h| ^ 4 / d ^ 4 := by
  unfold verticalOscillationCenteredBallFourthOrderResidualBound
  change ((4 * (12288 * (C : Real) / d ^ 4) +
    4 * (12288 * (C : Real) / d ^ 4)) * |h| ^ 4 / 12) = _
  ring

theorem verticalOscillationCenteredBallFourthOrderResidualBound_distanceScale
    (C : NNReal) (h rho : Real) (hh : h ≠ 0) (hrho : rho ≠ 0) :
    verticalOscillationCenteredBallFourthOrderResidualBound
        C h (|h| * rho) =
      8192 * (C : Real) / rho ^ 4 := by
  rw [verticalOscillationCenteredBallFourthOrderResidualBound_eq]
  field_simp [abs_ne_zero.mpr hh, hrho]


theorem LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnBall
    {Phi : Complex -> Complex} {c z : Complex} {h d : Real}
    (hd : 0 < d)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hrange : forall w, w ∈ ball c d ->
      0 <= (Phi w).im /\ (Phi w).im <= 1)
    (hpositiveOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 h) (ball c (d / 2)))
    (hnegativeOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 (-h)) (ball c (d / 2)))
    (hpositiveTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 h) (ball c (d / 2)))
    (hnegativeTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 (-h)) (ball c (d / 2))) :
    LocalDiagonalFourthOrderAnalyticData Phi z h
      (4 * (unitStripHalfBallFourthTensorBound d : Real))
      (4 * (unitStripHalfBallFourthTensorBound d : Real)) := by
  apply LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
    (ball c (d / 2)) Metric.isOpen_ball
    ((hPhi.mono (Metric.ball_subset_ball (by linarith))).analyticOnNhd
      Metric.isOpen_ball)
    (unitStripHalfBallFourthTensorBound d)
  · intro w hw
    exact isingFermionic_unitStrip_im_fourthTensor_le_on_halfBall
      Phi c d hd hPhi hrange w hw
  · exact hpositiveOne
  · exact hnegativeOne
  · exact hpositiveTwo
  · exact hnegativeTwo


theorem LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnBall
    {Phi : Complex -> Complex} {c z : Complex} {h d : Real}
    (C : NNReal) (hC : 0 < (C : Real)) (hd : 0 < d)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hosc : forall u, u ∈ ball c d -> forall v, v ∈ ball c d ->
      |(Phi u).im - (Phi v).im| <= (C : Real))
    (hpositiveOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 h) (ball c (d / 2)))
    (hnegativeOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 (-h)) (ball c (d / 2)))
    (hpositiveTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 h) (ball c (d / 2)))
    (hnegativeTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 (-h)) (ball c (d / 2))) :
    LocalDiagonalFourthOrderAnalyticData Phi z h
      (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real))
      (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) := by
  apply LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
    (ball c (d / 2)) Metric.isOpen_ball
    ((hPhi.mono (Metric.ball_subset_ball (by linarith))).analyticOnNhd
      Metric.isOpen_ball)
    (verticalOscillationHalfBallFourthTensorBound C d)
  · intro w hw
    exact isingFermionic_verticalOscillation_im_fourthTensor_le_on_halfBall
      Phi c d (C : Real) hd hC hPhi hosc w hw
  · exact hpositiveOne
  · exact hnegativeOne
  · exact hpositiveTwo
  · exact hnegativeTwo


theorem LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall
    {Phi : Complex -> Complex} {z : Complex} {h d : Real}
    (hd : 0 < d)
    (hmesh : 2 * |h| < d / 2)
    (hPhi : DifferentiableOn Complex Phi (ball z d))
    (hrange : forall w, w ∈ ball z d ->
      0 <= (Phi w).im /\ (Phi w).im <= 1) :
    LocalDiagonalFourthOrderAnalyticData Phi z h
      (4 * (unitStripHalfBallFourthTensorBound d : Real))
      (4 * (unitStripHalfBallFourthTensorBound d : Real)) := by
  have hcollar : Metric.cthickening (2 * |h|) ({z} : Set Complex) ⊆
      ball z (d / 2) := by
    rw [Metric.cthickening_singleton z (by positivity)]
    exact Metric.closedBall_subset_ball hmesh
  apply LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnBall
    hd hPhi hrange
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) h (le_refl _) true
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) (-h) (by simp) true
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) h (le_refl _) false
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) (-h) (by simp) false


theorem LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnCenteredBall
    {Phi : Complex -> Complex} {z : Complex} {h d : Real}
    (C : NNReal) (hC : 0 < (C : Real)) (hd : 0 < d)
    (hmesh : 2 * |h| < d / 2)
    (hPhi : DifferentiableOn Complex Phi (ball z d))
    (hosc : forall u, u ∈ ball z d -> forall v, v ∈ ball z d ->
      |(Phi u).im - (Phi v).im| <= (C : Real)) :
    LocalDiagonalFourthOrderAnalyticData Phi z h
      (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real))
      (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) := by
  have hcollar : Metric.cthickening (2 * |h|) ({z} : Set Complex) ⊆
      ball z (d / 2) := by
    rw [Metric.cthickening_singleton z (by positivity)]
    exact Metric.closedBall_subset_ball hmesh
  apply LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnBall
    C hC hd hPhi hosc
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) h (le_refl _) true
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) (-h) (by simp) true
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) h (le_refl _) false
  · simpa using diagonalSegment_mapsTo_of_cthickening
      (ball z (d / 2)) ({z} : Set Complex) (2 * |h|) hcollar
      z (by simp) (-h) (by simp) false


theorem fullSquareScaledVertex_sampledLaplacian_le_unitStripCenteredBall
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n) (d : Real)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hd : 0 < d) (hmesh : 2 * |mesh| < d / 2)
    (hPhi : DifferentiableOn Complex Phi
      (ball (fullSquareScaledVertexEmbedding n mesh x) d))
    (hrange : forall w,
      w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
        0 <= (Phi w).im /\ (Phi w).im <= 1) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <=
        unitStripCenteredBallFourthOrderResidualBound mesh d := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions n x hfixed hghost
  rw [fullSquareScaledVertex_sampledLaplacian_eq_stencil
    n mesh (fun z => (Phi z).im) x heast hnorth hwest hsouth]
  have H := LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall
    hd hmesh hPhi hrange
  simpa [unitStripCenteredBallFourthOrderResidualBound] using H.stencil


theorem fullSquareScaledFace_sampledLaplacian_le_unitStripCenteredBall
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n) (d : Real)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hd : 0 < d) (hmesh : 2 * |mesh| < d / 2)
    (hPhi : DifferentiableOn Complex Phi
      (ball (fullSquareScaledFaceEmbedding n mesh c) d))
    (hrange : forall w,
      w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
        0 <= (Phi w).im /\ (Phi w).im <= 1) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <=
        unitStripCenteredBallFourthOrderResidualBound mesh d := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates n c hfixed hghost
  rw [fullSquareScaledFace_sampledLaplacian_eq_stencil
    n mesh (fun z => (Phi z).im) c heast hnorth hwest hsouth]
  have H := LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall
    hd hmesh hPhi hrange
  simpa [unitStripCenteredBallFourthOrderResidualBound] using H.stencil


theorem fullSquareScaledVertex_sampledLaplacian_le_verticalOscillationCenteredBall
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n) (d : Real)
    (C : NNReal) (hC : 0 < (C : Real))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hd : 0 < d) (hmesh : 2 * |mesh| < d / 2)
    (hPhi : DifferentiableOn Complex Phi
      (ball (fullSquareScaledVertexEmbedding n mesh x) d))
    (hosc : forall u,
      u ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
      forall v, v ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
        |(Phi u).im - (Phi v).im| <= (C : Real)) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <=
        verticalOscillationCenteredBallFourthOrderResidualBound C mesh d := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions n x hfixed hghost
  rw [fullSquareScaledVertex_sampledLaplacian_eq_stencil
    n mesh (fun z => (Phi z).im) x heast hnorth hwest hsouth]
  have H :=
    LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnCenteredBall
      C hC hd hmesh hPhi hosc
  simpa [verticalOscillationCenteredBallFourthOrderResidualBound] using H.stencil


theorem fullSquareScaledFace_sampledLaplacian_le_verticalOscillationCenteredBall
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n) (d : Real)
    (C : NNReal) (hC : 0 < (C : Real))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hd : 0 < d) (hmesh : 2 * |mesh| < d / 2)
    (hPhi : DifferentiableOn Complex Phi
      (ball (fullSquareScaledFaceEmbedding n mesh c) d))
    (hosc : forall u,
      u ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
      forall v, v ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
        |(Phi u).im - (Phi v).im| <= (C : Real)) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <=
        verticalOscillationCenteredBallFourthOrderResidualBound C mesh d := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates n c hfixed hghost
  rw [fullSquareScaledFace_sampledLaplacian_eq_stencil
    n mesh (fun z => (Phi z).im) c heast hnorth hwest hsouth]
  have H :=
    LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnCenteredBall
      C hC hd hmesh hPhi hosc
  simpa [verticalOscillationCenteredBallFourthOrderResidualBound] using H.stencil


theorem fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic
    (n r : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall y,
      0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\
        (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
    (hball : 4 <= r ->
      let d := |mesh| * ((r + 1 : Nat) : Real)
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1)) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <=
        8192 / (((r + 1 : Nat) : Real) ^ 4) := by
  by_cases hr : 4 <= r
  · let rho : Real := ((r + 1 : Nat) : Real)
    have hrho : 0 < rho := by positivity
    obtain ⟨hPhi, hrange⟩ := hball hr
    have hmesh : 2 * |mesh| < (|mesh| * rho) / 2 := by
      have hm : 0 < |mesh| := abs_pos.mpr hmesh_ne
      have hrhoFive : 5 <= rho := by
        dsimp [rho]
        exact_mod_cast (show 5 <= r + 1 by omega)
      nlinarith
    have hlocal :=
      fullSquareScaledVertex_sampledLaplacian_le_unitStripCenteredBall
        n mesh Phi x (|mesh| * rho) hfixed hghost
        (mul_pos (abs_pos.mpr hmesh_ne) hrho) hmesh hPhi hrange
    rw [unitStripCenteredBallFourthOrderResidualBound_distanceScale
      mesh rho hmesh_ne hrho.ne'] at hlocal
    exact hlocal
  · have hsmall : r < 4 := by omega
    have hfour := fullSquareVertex_sampledLaplacian_le_four_of_unitRange
      n (fullSquareScaledVertexEmbedding n mesh) Phi hsampleRange x
    interval_cases r <;> apply hfour.trans <;> norm_num


theorem fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic
    (n r : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall z,
      0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\
        (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
    (hball : 4 <= r ->
      let d := |mesh| * ((r + 1 : Nat) : Real)
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1)) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <=
        8192 / (((r + 1 : Nat) : Real) ^ 4) := by
  by_cases hr : 4 <= r
  · let rho : Real := ((r + 1 : Nat) : Real)
    have hrho : 0 < rho := by positivity
    obtain ⟨hPhi, hrange⟩ := hball hr
    have hmesh : 2 * |mesh| < (|mesh| * rho) / 2 := by
      have hm : 0 < |mesh| := abs_pos.mpr hmesh_ne
      have hrhoFive : 5 <= rho := by
        dsimp [rho]
        exact_mod_cast (show 5 <= r + 1 by omega)
      nlinarith
    have hlocal :=
      fullSquareScaledFace_sampledLaplacian_le_unitStripCenteredBall
        n mesh Phi c (|mesh| * rho) hfixed hghost
        (mul_pos (abs_pos.mpr hmesh_ne) hrho) hmesh hPhi hrange
    rw [unitStripCenteredBallFourthOrderResidualBound_distanceScale
      mesh rho hmesh_ne hrho.ne'] at hlocal
    exact hlocal
  · have hsmall : r < 4 := by omega
    have hfour := fullSquareFace_sampledLaplacian_le_four_of_unitRange
      n (fullSquareScaledFaceEmbedding n mesh) Phi hsampleRange c
    interval_cases r <;> apply hfour.trans <;> norm_num


theorem fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation
    (n r : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n) (C : NNReal)
    (hCOne : 1 <= (C : Real))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall y,
      0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\
        (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
    (hball : 4 <= r ->
      let d := |mesh| * ((r + 1 : Nat) : Real)
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\
        (forall u,
          u ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
          forall v, v ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
            |(Phi u).im - (Phi v).im| <= (C : Real))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <=
        8192 * (C : Real) / (((r + 1 : Nat) : Real) ^ 4) := by
  have hC : 0 < (C : Real) := one_pos.trans_le hCOne
  by_cases hr : 4 <= r
  · let rho : Real := ((r + 1 : Nat) : Real)
    have hrho : 0 < rho := by positivity
    obtain ⟨hPhi, hosc⟩ := hball hr
    have hmesh : 2 * |mesh| < (|mesh| * rho) / 2 := by
      have hm : 0 < |mesh| := abs_pos.mpr hmesh_ne
      have hrhoFive : 5 <= rho := by
        dsimp [rho]
        exact_mod_cast (show 5 <= r + 1 by omega)
      nlinarith
    have hlocal :=
      fullSquareScaledVertex_sampledLaplacian_le_verticalOscillationCenteredBall
        n mesh Phi x (|mesh| * rho) C hC hfixed hghost
        (mul_pos (abs_pos.mpr hmesh_ne) hrho) hmesh hPhi hosc
    rw [verticalOscillationCenteredBallFourthOrderResidualBound_distanceScale
      C mesh rho hmesh_ne hrho.ne'] at hlocal
    exact hlocal
  · have hsmall : r < 4 := by omega
    have hfour := fullSquareVertex_sampledLaplacian_le_four_of_unitRange
      n (fullSquareScaledVertexEmbedding n mesh) Phi hsampleRange x
    interval_cases r <;> apply hfour.trans <;> norm_num <;> nlinarith


theorem fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation
    (n r : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n) (C : NNReal)
    (hCOne : 1 <= (C : Real))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall z,
      0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\
        (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
    (hball : 4 <= r ->
      let d := |mesh| * ((r + 1 : Nat) : Real)
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\
        (forall u,
          u ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
          forall v, v ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
            |(Phi u).im - (Phi v).im| <= (C : Real))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <=
        8192 * (C : Real) / (((r + 1 : Nat) : Real) ^ 4) := by
  have hC : 0 < (C : Real) := one_pos.trans_le hCOne
  by_cases hr : 4 <= r
  · let rho : Real := ((r + 1 : Nat) : Real)
    have hrho : 0 < rho := by positivity
    obtain ⟨hPhi, hosc⟩ := hball hr
    have hmesh : 2 * |mesh| < (|mesh| * rho) / 2 := by
      have hm : 0 < |mesh| := abs_pos.mpr hmesh_ne
      have hrhoFive : 5 <= rho := by
        dsimp [rho]
        exact_mod_cast (show 5 <= r + 1 by omega)
      nlinarith
    have hlocal :=
      fullSquareScaledFace_sampledLaplacian_le_verticalOscillationCenteredBall
        n mesh Phi c (|mesh| * rho) C hC hfixed hghost
        (mul_pos (abs_pos.mpr hmesh_ne) hrho) hmesh hPhi hosc
    rw [verticalOscillationCenteredBallFourthOrderResidualBound_distanceScale
      C mesh rho hmesh_ne hrho.ne'] at hlocal
    exact hlocal
  · have hsmall : r < 4 := by omega
    have hfour := fullSquareFace_sampledLaplacian_le_four_of_unitRange
      n (fullSquareScaledFaceEmbedding n mesh) Phi hsampleRange c
    interval_cases r <;> apply hfour.trans <;> norm_num <;> nlinarith


theorem vertexSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0) :
    vertexSpatialTargetResidual n
        (vertexSampledImaginaryTarget n
          (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) =
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| := by
  have hsampled : vertexSampledImaginaryTarget n
      (fullSquareScaledVertexEmbedding n mesh) Phi =
      isingFiniteGhostExtension 1
        (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) := by
    funext z
    cases z <;> rfl
  rw [hsampled]
  unfold vertexSpatialTargetResidual vertexDirichletBoundary
    vertexGhostConductance
  simp only [isingFiniteGhostBoundaryWith, hfixed, ↓reduceIte]
  rw [isingFiniteGhostLaplacian_some]
  simp [isingFermionicGhostRate, hghost]


theorem faceSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0) :
    faceSpatialTargetResidual n
        (faceSampledImaginaryTarget n
          (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) =
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| := by
  have hsampled : faceSampledImaginaryTarget n
      (fullSquareScaledFaceEmbedding n mesh) Phi =
      isingFiniteGhostExtension 0
        (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) := by
    funext z
    cases z <;> rfl
  rw [hsampled]
  unfold faceSpatialTargetResidual faceDirichletBoundary faceGhostConductance
  simp only [isingFiniteGhostBoundaryWith, hfixed, ↓reduceIte]
  rw [isingFiniteGhostLaplacian_some]
  simp [isingFermionicGhostRate, hghost]


theorem vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall y,
      0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\
        (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
    (hball : 4 <= vertexEndpointRadialShell n (some x) ->
      let d := |mesh| *
        (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1)) :
    vertexSpatialTargetResidual n
        (vertexSampledImaginaryTarget n
          (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) <=
      8192 / (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real) ^ 4) := by
  rw [vertexSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    n mesh Phi x hfixed hghost]
  exact fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic
    n (vertexEndpointRadialShell n (some x)) mesh Phi x hfixed hghost
      hmesh_ne hsampleRange hball


theorem faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall z,
      0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\
        (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
    (hball : 4 <= faceEndpointRadialShell n (some c) ->
      let d := |mesh| *
        (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1)) :
    faceSpatialTargetResidual n
        (faceSampledImaginaryTarget n
          (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) <=
      8192 / (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real) ^ 4) := by
  rw [faceSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    n mesh Phi c hfixed hghost]
  exact fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic
    n (faceEndpointRadialShell n (some c)) mesh Phi c hfixed hghost
      hmesh_ne hsampleRange hball


theorem vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_verticalOscillation
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (x : FKIsingSquareFullVertexNode n) (C : NNReal)
    (hCOne : 1 <= (C : Real))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall y,
      0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\
        (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
    (hball : 4 <= vertexEndpointRadialShell n (some x) ->
      let d := |mesh| *
        (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\
        (forall u,
          u ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
          forall v, v ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
            |(Phi u).im - (Phi v).im| <= (C : Real))) :
    vertexSpatialTargetResidual n
        (vertexSampledImaginaryTarget n
          (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) <=
      8192 * (C : Real) /
        (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real) ^ 4) := by
  rw [vertexSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    n mesh Phi x hfixed hghost]
  exact
    fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation
      n (vertexEndpointRadialShell n (some x)) mesh Phi x C hCOne
        hfixed hghost hmesh_ne hsampleRange hball


theorem faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_verticalOscillation
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (c : FKIsingSquareFullFaceNode n) (C : NNReal)
    (hCOne : 1 <= (C : Real))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall z,
      0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\
        (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
    (hball : 4 <= faceEndpointRadialShell n (some c) ->
      let d := |mesh| *
        (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\
        (forall u,
          u ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
          forall v, v ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
            |(Phi u).im - (Phi v).im| <= (C : Real))) :
    faceSpatialTargetResidual n
        (faceSampledImaginaryTarget n
          (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) <=
      8192 * (C : Real) /
        (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real) ^ 4) := by
  rw [faceSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk
    n mesh Phi c hfixed hghost]
  exact
    fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation
      n (faceEndpointRadialShell n (some c)) mesh Phi c C hCOne
        hfixed hghost hmesh_ne hsampleRange hball


theorem vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall y,
      0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\
        (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
    (hball : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      4 <= vertexEndpointRadialShell n (some x) ->
      let d := |mesh| *
        (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1))
    (hghostResidual : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x ≠ 0 ->
      vertexSpatialTargetResidual n
          (vertexSampledImaginaryTarget n
            (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) <=
        8192 /
          (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real) ^ 4)) :
    forall z,
      vertexSpatialTargetResidual n
          (vertexSampledImaginaryTarget n
            (fullSquareScaledVertexEmbedding n mesh) Phi) z <=
        8192 / (((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 4) := by
  intro z
  cases z with
  | none =>
      simp [vertexSpatialTargetResidual, vertexDirichletBoundary,
        isingFiniteGhostBoundaryWith]
  | some x =>
      by_cases hfixed : fkIsingSquareFullVertexFixedBoundary n x
      · have hzero : vertexSpatialTargetResidual n
            (vertexSampledImaginaryTarget n
              (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) = 0 := by
          simp [vertexSpatialTargetResidual, vertexDirichletBoundary,
            isingFiniteGhostBoundaryWith, hfixed]
        rw [hzero]
        positivity
      · by_cases hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0
        · exact
            vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk
              n mesh Phi x hfixed hghost hmesh_ne hsampleRange
                (hball x hfixed hghost)
        · exact hghostResidual x hfixed hghost


theorem faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic
    (n : Nat) (mesh : Real) (Phi : Complex -> Complex)
    (hmesh_ne : mesh ≠ 0)
    (hsampleRange : forall c,
      0 <= (Phi (fullSquareScaledFaceEmbedding n mesh c)).im /\
        (Phi (fullSquareScaledFaceEmbedding n mesh c)).im <= 1)
    (hball : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      4 <= faceEndpointRadialShell n (some c) ->
      let d := |mesh| *
        (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real))
      DifferentiableOn Complex Phi
          (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\
        (forall w,
          w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d ->
            0 <= (Phi w).im /\ (Phi w).im <= 1))
    (hghostResidual : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c ≠ 0 ->
      faceSpatialTargetResidual n
          (faceSampledImaginaryTarget n
            (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) <=
        8192 /
          (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real) ^ 4)) :
    forall z,
      faceSpatialTargetResidual n
          (faceSampledImaginaryTarget n
            (fullSquareScaledFaceEmbedding n mesh) Phi) z <=
        8192 / (((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 4) := by
  intro z
  cases z with
  | none =>
      simp [faceSpatialTargetResidual, faceDirichletBoundary,
        isingFiniteGhostBoundaryWith]
  | some c =>
      by_cases hfixed : fkIsingSquareFullFaceFixedBoundary n c
      · have hzero : faceSpatialTargetResidual n
            (faceSampledImaginaryTarget n
              (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) = 0 := by
          simp [faceSpatialTargetResidual, faceDirichletBoundary,
            isingFiniteGhostBoundaryWith, hfixed]
        rw [hzero]
        positivity
      · by_cases hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0
        · exact
            faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk
              n mesh Phi c hfixed hghost hmesh_ne hsampleRange
                (hball c hfixed hghost)
        · exact hghostResidual c hfixed hghost


end FKIsingSquareBoundaryLayerCoordinateOneForm
end StatMech.Universality
