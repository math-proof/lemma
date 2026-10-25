import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStripCauchyFourthOrder.Part2
open Metric StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFermionic_verticalOscillation_cauchy_fourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma isingFermionic_verticalOscillation_cauchy_fourth_eq
  {c : Complex}
  {d C : Real}
-- given
  (Phi : Complex -> Complex)
  (hd : 0 < d)
  (hC : 0 < C)
  (hPhi : DifferentiableOn Complex Phi (ball c d))
  (hosc : forall z, z ∈ ball c d -> |(Phi z).im - (Phi c).im| <= C) :
-- imply
  ‖iteratedDeriv 4 Phi c‖ <= 768 * C / d ^ 4 := by
-- proof
  apply isingFermionic_verticalOscillation_cauchy_fourth Phi c d C hd hC hPhi hosc

/--
[isingFermionic_strip_cauchy_fourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma isingFermionic_strip_cauchy_fourth_eq
  {c : Complex}
  {d : Real}
-- given
  (Phi : Complex -> Complex)
  (hd : 0 < d)
  (hPhi : DifferentiableOn Complex Phi (ball c d))
  (hrange : forall z, z ∈ ball c d -> 0 <= (Phi z).im /\ (Phi z).im <= 1) :
-- imply
  ‖iteratedDeriv 4 Phi c‖ <= 768 / d ^ 4 := by
-- proof
  apply isingFermionic_strip_cauchy_fourth Phi c d hd hPhi hrange

/--
[isingFermionic_norm_iteratedFDeriv_real_im_le_iteratedDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma isingFermionic_norm_iteratedFDeriv_real_im_le_iteratedDeriv_eq
  {c : Complex}
-- given
  (Phi : Complex -> Complex)
  (hPhi : ContDiffAt Complex 4 Phi c) :
-- imply
  ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <= ‖iteratedDeriv 4 Phi c‖ := by
-- proof
  apply isingFermionic_norm_iteratedFDeriv_real_im_le_iteratedDeriv Phi c hPhi

/--
[isingFermionic_verticalOscillation_im_fourth_tensor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma isingFermionic_verticalOscillation_im_fourth_tensor_eq
  {c : Complex}
  {d C : Real}
-- given
  (Phi : Complex -> Complex)
  (hd : 0 < d)
  (hC : 0 < C)
  (hPhi : DifferentiableOn Complex Phi (ball c d))
  (hosc : forall z, z ∈ ball c d -> |(Phi z).im - (Phi c).im| <= C) :
-- imply
  ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <= 768 * C / d ^ 4 := by
-- proof
  apply isingFermionic_verticalOscillation_im_fourth_tensor Phi c d C hd hC hPhi hosc

/--
[isingFermionic_strip_im_fourth_tensor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma isingFermionic_strip_im_fourth_tensor_eq
  {c : Complex}
  {d : Real}
-- given
  (Phi : Complex -> Complex)
  (hd : 0 < d)
  (hPhi : DifferentiableOn Complex Phi (ball c d))
  (hrange : forall z, z ∈ ball c d -> 0 <= (Phi z).im /\ (Phi z).im <= 1) :
-- imply
  ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <= 768 / d ^ 4 := by
-- proof
  apply isingFermionic_strip_im_fourth_tensor Phi c d hd hPhi hrange

/--
[isingFermionic_ball_half_subset_ball_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma isingFermionic_ball_half_subset_ball_of_mem_eq
  {c w : Complex}
  {d : Real}
-- given
  (hw : w ∈ ball c (d / 2)) :
-- imply
  ball w (d / 2) ⊆ ball c d := by
-- proof
  apply isingFermionic_ball_half_subset_ball_of_mem hw

/--
[isingFermionic_verticalOscillation_im_fourthTensor_le_on_halfBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma isingFermionic_verticalOscillation_im_fourthTensor_le_on_halfBall_eq
  {c : Complex}
  {d C : Real}
-- given
  (Phi : Complex -> Complex)
  (hd : 0 < d)
  (hC : 0 < C)
  (hPhi : DifferentiableOn Complex Phi (ball c d))
  (hosc : forall z, z ∈ ball c d -> forall w, w ∈ ball c d -> |(Phi z).im - (Phi w).im| <= C) :
-- imply
  forall w, w ∈ ball c (d / 2) -> ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= 12288 * C / d ^ 4 := by
-- proof
  apply isingFermionic_verticalOscillation_im_fourthTensor_le_on_halfBall Phi c d C hd hC hPhi hosc

/--
[isingFermionic_unitStrip_im_fourthTensor_le_on_halfBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma isingFermionic_unitStrip_im_fourthTensor_le_on_halfBall_eq
  {c : Complex}
  {d : Real}
-- given
  (Phi : Complex -> Complex)
  (hd : 0 < d)
  (hPhi : DifferentiableOn Complex Phi (ball c d))
  (hrange : forall z, z ∈ ball c d -> 0 <= (Phi z).im /\ (Phi z).im <= 1) :
-- imply
  forall w, w ∈ ball c (d / 2) -> ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= 12288 / d ^ 4 := by
-- proof
  apply isingFermionic_unitStrip_im_fourthTensor_le_on_halfBall Phi c d hd hPhi hrange

/--
[unitStripCenteredBallFourthOrderResidualBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma unitStripCenteredBallFourthOrderResidualBound_eq_eq
-- given
  (h d : Real) :
-- imply
  unitStripCenteredBallFourthOrderResidualBound h d = 8192 * |h| ^ 4 / d ^ 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.unitStripCenteredBallFourthOrderResidualBound_eq h d

/--
[unitStripCenteredBallFourthOrderResidualBound_distanceScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma unitStripCenteredBallFourthOrderResidualBound_distanceScale_eq
-- given
  (h rho : Real)
  (hh : h ≠ 0)
  (hrho : rho ≠ 0) :
-- imply
  unitStripCenteredBallFourthOrderResidualBound h (|h| * rho) = 8192 / rho ^ 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.unitStripCenteredBallFourthOrderResidualBound_distanceScale h rho hh hrho

/--
[verticalOscillationCenteredBallFourthOrderResidualBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma verticalOscillationCenteredBallFourthOrderResidualBound_eq_eq
  {C : NNReal}
-- given
  (h d : Real) :
-- imply
  verticalOscillationCenteredBallFourthOrderResidualBound C h d = 8192 * (C : Real) * |h| ^ 4 / d ^ 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.verticalOscillationCenteredBallFourthOrderResidualBound_eq C h d

/--
[verticalOscillationCenteredBallFourthOrderResidualBound_distanceScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma verticalOscillationCenteredBallFourthOrderResidualBound_distanceScale_eq
  {C : NNReal}
-- given
  (h rho : Real)
  (hh : h ≠ 0)
  (hrho : rho ≠ 0) :
-- imply
  verticalOscillationCenteredBallFourthOrderResidualBound C h (|h| * rho) = 8192 * (C : Real) / rho ^ 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.verticalOscillationCenteredBallFourthOrderResidualBound_distanceScale C h rho hh hrho

/--
[LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma ofUnitStripOnBall_eq
  {Phi : Complex -> Complex}
  {c z : Complex}
  {h d : Real}
-- given
  (hd : 0 < d)
  (hPhi : DifferentiableOn Complex Phi (ball c d))
  (hrange : forall w, w ∈ ball c d -> 0 <= (Phi w).im /\ (Phi w).im <= 1)
  (hpositiveOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) (Set.uIcc 0 h) (ball c (d / 2)))
  (hnegativeOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) (Set.uIcc 0 (-h)) (ball c (d / 2)))
  (hpositiveTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) (Set.uIcc 0 h) (ball c (d / 2)))
  (hnegativeTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) (Set.uIcc 0 (-h)) (ball c (d / 2))) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h (4 * (unitStripHalfBallFourthTensorBound d : Real)) (4 * (unitStripHalfBallFourthTensorBound d : Real)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnBall hd hPhi hrange hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo

/--
[LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma ofVerticalOscillationOnBall_eq
  {Phi : Complex -> Complex}
  {c z : Complex}
  {h d : Real}
  {C : NNReal}
-- given
  (hC : 0 < (C : Real))
  (hd : 0 < d)
  (hPhi : DifferentiableOn Complex Phi (ball c d))
  (hosc : forall u, u ∈ ball c d -> forall v, v ∈ ball c d -> |(Phi u).im - (Phi v).im| <= (C : Real))
  (hpositiveOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) (Set.uIcc 0 h) (ball c (d / 2)))
  (hnegativeOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) (Set.uIcc 0 (-h)) (ball c (d / 2)))
  (hpositiveTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) (Set.uIcc 0 h) (ball c (d / 2)))
  (hnegativeTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) (Set.uIcc 0 (-h)) (ball c (d / 2))) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnBall C hC hd hPhi hosc hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo

/--
[LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma ofUnitStripOnCenteredBall_eq
  {Phi : Complex -> Complex}
  {z : Complex}
  {h d : Real}
-- given
  (hd : 0 < d)
  (hmesh : 2 * |h| < d / 2)
  (hPhi : DifferentiableOn Complex Phi (ball z d))
  (hrange : forall w, w ∈ ball z d -> 0 <= (Phi w).im /\ (Phi w).im <= 1) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h (4 * (unitStripHalfBallFourthTensorBound d : Real)) (4 * (unitStripHalfBallFourthTensorBound d : Real)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall hd hmesh hPhi hrange

/--
[LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnCenteredBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma ofVerticalOscillationOnCenteredBall_eq
  {Phi : Complex -> Complex}
  {z : Complex}
  {h d : Real}
  {C : NNReal}
-- given
  (hC : 0 < (C : Real))
  (hd : 0 < d)
  (hmesh : 2 * |h| < d / 2)
  (hPhi : DifferentiableOn Complex Phi (ball z d))
  (hosc : forall u, u ∈ ball z d -> forall v, v ∈ ball z d -> |(Phi u).im - (Phi v).im| <= (C : Real)) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) (4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofVerticalOscillationOnCenteredBall C hC hd hmesh hPhi hosc

/--
[fullSquareScaledVertex_sampledLaplacian_le_unitStripCenteredBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma fullSquareScaledVertex_sampledLaplacian_le_unitStripCenteredBall_eq
  {n : Nat}
  {mesh : Real}
  {x : FKIsingSquareFullVertexNode n}
  {d : Real}
-- given
  (Phi : Complex -> Complex)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
  (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
  (hd : 0 < d)
  (hmesh : 2 * |mesh| < d / 2)
  (hPhi : DifferentiableOn Complex Phi (ball (fullSquareScaledVertexEmbedding n mesh x) d))
  (hrange : forall w, w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d -> 0 <= (Phi w).im /\ (Phi w).im <= 1) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <= unitStripCenteredBallFourthOrderResidualBound mesh d := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertex_sampledLaplacian_le_unitStripCenteredBall n mesh Phi x d hfixed hghost hd hmesh hPhi hrange

/--
[fullSquareScaledFace_sampledLaplacian_le_unitStripCenteredBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma fullSquareScaledFace_sampledLaplacian_le_unitStripCenteredBall_eq
  {n : Nat}
  {mesh : Real}
  {c : FKIsingSquareFullFaceNode n}
  {d : Real}
-- given
  (Phi : Complex -> Complex)
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
  (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
  (hd : 0 < d)
  (hmesh : 2 * |mesh| < d / 2)
  (hPhi : DifferentiableOn Complex Phi (ball (fullSquareScaledFaceEmbedding n mesh c) d))
  (hrange : forall w, w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d -> 0 <= (Phi w).im /\ (Phi w).im <= 1) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <= unitStripCenteredBallFourthOrderResidualBound mesh d := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFace_sampledLaplacian_le_unitStripCenteredBall n mesh Phi c d hfixed hghost hd hmesh hPhi hrange

/--
[fullSquareScaledVertex_sampledLaplacian_le_verticalOscillationCenteredBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma fullSquareScaledVertex_sampledLaplacian_le_verticalOscillationCenteredBall_eq
  {n : Nat}
  {mesh : Real}
  {x : FKIsingSquareFullVertexNode n}
  {d : Real}
  {C : NNReal}
-- given
  (Phi : Complex -> Complex)
  (hC : 0 < (C : Real))
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
  (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
  (hd : 0 < d)
  (hmesh : 2 * |mesh| < d / 2)
  (hPhi : DifferentiableOn Complex Phi (ball (fullSquareScaledVertexEmbedding n mesh x) d))
  (hosc : forall u, u ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d -> forall v, v ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d -> |(Phi u).im - (Phi v).im| <= (C : Real)) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <= verticalOscillationCenteredBallFourthOrderResidualBound C mesh d := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertex_sampledLaplacian_le_verticalOscillationCenteredBall n mesh Phi x d C hC hfixed hghost hd hmesh hPhi hosc

/--
[fullSquareScaledFace_sampledLaplacian_le_verticalOscillationCenteredBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma fullSquareScaledFace_sampledLaplacian_le_verticalOscillationCenteredBall_eq
  {n : Nat}
  {mesh : Real}
  {c : FKIsingSquareFullFaceNode n}
  {d : Real}
  {C : NNReal}
-- given
  (Phi : Complex -> Complex)
  (hC : 0 < (C : Real))
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
  (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
  (hd : 0 < d)
  (hmesh : 2 * |mesh| < d / 2)
  (hPhi : DifferentiableOn Complex Phi (ball (fullSquareScaledFaceEmbedding n mesh c) d))
  (hosc : forall u, u ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d -> forall v, v ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d -> |(Phi u).im - (Phi v).im| <= (C : Real)) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <= verticalOscillationCenteredBallFourthOrderResidualBound C mesh d := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFace_sampledLaplacian_le_verticalOscillationCenteredBall n mesh Phi c d C hC hfixed hghost hd hmesh hPhi hosc

/--
[fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic_eq
  {n r : Nat}
  {mesh : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (Phi : Complex -> Complex)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
  (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
  (hmesh_ne : mesh ≠ 0)
  (hsampleRange : forall y, 0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\ (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
  (hball : 4 <= r -> let d := |mesh| * ((r + 1 : Nat) : Real) DifferentiableOn Complex Phi (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\ (forall w, w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d -> 0 <= (Phi w).im /\ (Phi w).im <= 1)) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <= 8192 / (((r + 1 : Nat) : Real) ^ 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic n r mesh Phi x hfixed hghost hmesh_ne hsampleRange hball

/--
[fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic_eq
  {n r : Nat}
  {mesh : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (Phi : Complex -> Complex)
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
  (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
  (hmesh_ne : mesh ≠ 0)
  (hsampleRange : forall z, 0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\ (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
  (hball : 4 <= r -> let d := |mesh| * ((r + 1 : Nat) : Real) DifferentiableOn Complex Phi (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\ (forall w, w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d -> 0 <= (Phi w).im /\ (Phi w).im <= 1)) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <= 8192 / (((r + 1 : Nat) : Real) ^ 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic n r mesh Phi c hfixed hghost hmesh_ne hsampleRange hball

/--
[fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation_eq
  {n r : Nat}
  {mesh : Real}
  {x : FKIsingSquareFullVertexNode n}
  {C : NNReal}
-- given
  (Phi : Complex -> Complex)
  (hCOne : 1 <= (C : Real))
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
  (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
  (hmesh_ne : mesh ≠ 0)
  (hsampleRange : forall y, 0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\ (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
  (hball : 4 <= r -> let d := |mesh| * ((r + 1 : Nat) : Real) DifferentiableOn Complex Phi (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\ (forall u, u ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d -> forall v, v ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d -> |(Phi u).im - (Phi v).im| <= (C : Real))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| <= 8192 * (C : Real) / (((r + 1 : Nat) : Real) ^ 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertex_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation n r mesh Phi x C hCOne hfixed hghost hmesh_ne hsampleRange hball

/--
[fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation_eq
  {n r : Nat}
  {mesh : Real}
  {c : FKIsingSquareFullFaceNode n}
  {C : NNReal}
-- given
  (Phi : Complex -> Complex)
  (hCOne : 1 <= (C : Real))
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
  (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
  (hmesh_ne : mesh ≠ 0)
  (hsampleRange : forall z, 0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\ (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
  (hball : 4 <= r -> let d := |mesh| * ((r + 1 : Nat) : Real) DifferentiableOn Complex Phi (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\ (forall u, u ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d -> forall v, v ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d -> |(Phi u).im - (Phi v).im| <= (C : Real))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| <= 8192 * (C : Real) / (((r + 1 : Nat) : Real) ^ 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFace_sampledLaplacian_le_endpointRadiusQuartic_of_verticalOscillation n r mesh Phi c C hCOne hfixed hghost hmesh_ne hsampleRange hball

/--
[vertexSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma vertexSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk_eq
  {n : Nat}
  {mesh : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (Phi : Complex -> Complex)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
  (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0) :
-- imply
  vertexSpatialTargetResidual n (vertexSampledImaginaryTarget n (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) = |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (fullSquareScaledVertexEmbedding n mesh y)).im) x| := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk n mesh Phi x hfixed hghost

/--
[faceSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma faceSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk_eq
  {n : Nat}
  {mesh : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (Phi : Complex -> Complex)
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
  (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0) :
-- imply
  faceSpatialTargetResidual n (faceSampledImaginaryTarget n (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) = |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun z => (Phi (fullSquareScaledFaceEmbedding n mesh z)).im) c| := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidual_sampled_eq_graphLaplacian_of_bulk n mesh Phi c hfixed hghost

/--
[vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_eq
  {n : Nat}
  {mesh : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (Phi : Complex -> Complex)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
  (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
  (hmesh_ne : mesh ≠ 0)
  (hsampleRange : forall y, 0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\ (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
  (hball : 4 <= vertexEndpointRadialShell n (some x) -> let d := |mesh| * (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real)) DifferentiableOn Complex Phi (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\ (forall w, w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d -> 0 <= (Phi w).im /\ (Phi w).im <= 1)) :
-- imply
  vertexSpatialTargetResidual n (vertexSampledImaginaryTarget n (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) <= 8192 / (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real) ^ 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk n mesh Phi x hfixed hghost hmesh_ne hsampleRange hball

/--
[faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_eq
  {n : Nat}
  {mesh : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (Phi : Complex -> Complex)
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
  (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
  (hmesh_ne : mesh ≠ 0)
  (hsampleRange : forall z, 0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\ (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
  (hball : 4 <= faceEndpointRadialShell n (some c) -> let d := |mesh| * (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real)) DifferentiableOn Complex Phi (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\ (forall w, w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d -> 0 <= (Phi w).im /\ (Phi w).im <= 1)) :
-- imply
  faceSpatialTargetResidual n (faceSampledImaginaryTarget n (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) <= 8192 / (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real) ^ 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk n mesh Phi c hfixed hghost hmesh_ne hsampleRange hball

/--
[vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_verticalOscillation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_verticalOscillation_eq
  {n : Nat}
  {mesh : Real}
  {x : FKIsingSquareFullVertexNode n}
  {C : NNReal}
-- given
  (Phi : Complex -> Complex)
  (hCOne : 1 <= (C : Real))
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n x))
  (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0)
  (hmesh_ne : mesh ≠ 0)
  (hsampleRange : forall y, 0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\ (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
  (hball : 4 <= vertexEndpointRadialShell n (some x) -> let d := |mesh| * (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real)) DifferentiableOn Complex Phi (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\ (forall u, u ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d -> forall v, v ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d -> |(Phi u).im - (Phi v).im| <= (C : Real))) :
-- imply
  vertexSpatialTargetResidual n (vertexSampledImaginaryTarget n (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) <= 8192 * (C : Real) / (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real) ^ 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_verticalOscillation n mesh Phi x C hCOne hfixed hghost hmesh_ne hsampleRange hball

/--
[faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_verticalOscillation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_verticalOscillation_eq
  {n : Nat}
  {mesh : Real}
  {c : FKIsingSquareFullFaceNode n}
  {C : NNReal}
-- given
  (Phi : Complex -> Complex)
  (hCOne : 1 <= (C : Real))
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n c))
  (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0)
  (hmesh_ne : mesh ≠ 0)
  (hsampleRange : forall z, 0 <= (Phi (fullSquareScaledFaceEmbedding n mesh z)).im /\ (Phi (fullSquareScaledFaceEmbedding n mesh z)).im <= 1)
  (hball : 4 <= faceEndpointRadialShell n (some c) -> let d := |mesh| * (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real)) DifferentiableOn Complex Phi (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\ (forall u, u ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d -> forall v, v ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d -> |(Phi u).im - (Phi v).im| <= (C : Real))) :
-- imply
  faceSpatialTargetResidual n (faceSampledImaginaryTarget n (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) <= 8192 * (C : Real) / (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real) ^ 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_of_bulk_verticalOscillation n mesh Phi c C hCOne hfixed hghost hmesh_ne hsampleRange hball

/--
[vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic_eq
  {n : Nat}
  {mesh : Real}
-- given
  (Phi : Complex -> Complex)
  (hmesh_ne : mesh ≠ 0)
  (hsampleRange : forall y, 0 <= (Phi (fullSquareScaledVertexEmbedding n mesh y)).im /\ (Phi (fullSquareScaledVertexEmbedding n mesh y)).im <= 1)
  (hball : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> fkIsingSquareFullVertexGhostMultiplicity n x = 0 -> 4 <= vertexEndpointRadialShell n (some x) -> let d := |mesh| * (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real)) DifferentiableOn Complex Phi (ball (fullSquareScaledVertexEmbedding n mesh x) d) /\ (forall w, w ∈ ball (fullSquareScaledVertexEmbedding n mesh x) d -> 0 <= (Phi w).im /\ (Phi w).im <= 1))
  (hghostResidual : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> fkIsingSquareFullVertexGhostMultiplicity n x ≠ 0 -> vertexSpatialTargetResidual n (vertexSampledImaginaryTarget n (fullSquareScaledVertexEmbedding n mesh) Phi) (some x) <= 8192 / (((vertexEndpointRadialShell n (some x) + 1 : Nat) : Real) ^ 4)) :
-- imply
  forall z, vertexSpatialTargetResidual n (vertexSampledImaginaryTarget n (fullSquareScaledVertexEmbedding n mesh) Phi) z <= 8192 / (((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidual_sampled_le_endpointRadiusQuartic n mesh Phi hmesh_ne hsampleRange hball hghostResidual

/--
[faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean)
-/
@[path]
private lemma faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic_eq
  {n : Nat}
  {mesh : Real}
-- given
  (Phi : Complex -> Complex)
  (hmesh_ne : mesh ≠ 0)
  (hsampleRange : forall c, 0 <= (Phi (fullSquareScaledFaceEmbedding n mesh c)).im /\ (Phi (fullSquareScaledFaceEmbedding n mesh c)).im <= 1)
  (hball : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> fkIsingSquareFullFaceGhostMultiplicity n c = 0 -> 4 <= faceEndpointRadialShell n (some c) -> let d := |mesh| * (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real)) DifferentiableOn Complex Phi (ball (fullSquareScaledFaceEmbedding n mesh c) d) /\ (forall w, w ∈ ball (fullSquareScaledFaceEmbedding n mesh c) d -> 0 <= (Phi w).im /\ (Phi w).im <= 1))
  (hghostResidual : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> fkIsingSquareFullFaceGhostMultiplicity n c ≠ 0 -> faceSpatialTargetResidual n (faceSampledImaginaryTarget n (fullSquareScaledFaceEmbedding n mesh) Phi) (some c) <= 8192 / (((faceEndpointRadialShell n (some c) + 1 : Nat) : Real) ^ 4)) :
-- imply
  forall z, faceSpatialTargetResidual n (faceSampledImaginaryTarget n (fullSquareScaledFaceEmbedding n mesh) Phi) z <= 8192 / (((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidual_sampled_le_endpointRadiusQuartic n mesh Phi hmesh_ne hsampleRange hball hghostResidual


-- created on 2026-10-23
