import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[LocalDiagonalFourthOrderAnalyticData.stencil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma stencil_eq
  {Phi : Complex -> Complex}
  {z : Complex}
  {h boundOne boundTwo : Real}
  {H : LocalDiagonalFourthOrderAnalyticData Phi z h boundOne boundTwo} :
-- imply
  |complexDirectionalFourNeighborStencil (fun w => (Phi w).im) z (1 + Complex.I) (1 - Complex.I) h| <= (boundOne + boundTwo) * |h| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.stencil H

/--
[LocalDiagonalFourthOrderAnalyticData.ofOpenLineData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma ofOpenLineData_eq
  {Phi : Complex -> Complex}
  {z : Complex}
  {h boundOne boundTwo : Real}
  {UOne UTwo : Set Real}
-- given
  (hUOne : IsOpen UOne)
  (hUTwo : IsOpen UTwo)
  (hzeroOne : 0 ∈ UOne)
  (hzeroTwo : 0 ∈ UTwo)
  (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
  (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
  (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
  (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
  (hsmoothOne : ContDiffOn Real 4 (fun t : Real => (Phi (z + (t : Complex) * (1 + Complex.I))).im) UOne)
  (hsmoothTwo : ContDiffOn Real 4 (fun t : Real => (Phi (z + (t : Complex) * (1 - Complex.I))).im) UTwo)
  (hboundOne : forall t, t ∈ UOne -> |iteratedDeriv 4 (fun s : Real => (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
  (hboundTwo : forall t, t ∈ UTwo -> |iteratedDeriv 4 (fun s : Real => (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo)
  (hanalytic : AnalyticAt Complex Phi z) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h boundOne boundTwo where one := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofOpenLineData UOne UTwo hUOne hUTwo hzeroOne hzeroTwo hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo hsmoothOne hsmoothTwo hboundOne hboundTwo hanalytic

/--
[LocalDiagonalFourthOrderAnalyticData.ofOpenAmbientData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma ofOpenAmbientData_eq
  {Phi : Complex -> Complex}
  {z : Complex}
  {h boundOne boundTwo : Real}
  {U : Set Complex}
  {UOne UTwo : Set Real}
-- given
  (hUOne : IsOpen UOne)
  (hUTwo : IsOpen UTwo)
  (hzeroOne : 0 ∈ UOne)
  (hzeroTwo : 0 ∈ UTwo)
  (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
  (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
  (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
  (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
  (hmapsOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) UOne U)
  (hmapsTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) UTwo U)
  (hsmooth : ContDiffOn Real 4 (fun w => (Phi w).im) U)
  (hboundOne : forall t, t ∈ UOne -> |iteratedDeriv 4 (fun s : Real => (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
  (hboundTwo : forall t, t ∈ UTwo -> |iteratedDeriv 4 (fun s : Real => (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo)
  (hanalytic : AnalyticAt Complex Phi z) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h boundOne boundTwo := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofOpenAmbientData U UOne UTwo hUOne hUTwo hzeroOne hzeroTwo hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo hmapsOne hmapsTwo hsmooth hboundOne hboundTwo hanalytic

/--
[LocalDiagonalFourthOrderAnalyticData.ofAnalyticOnNhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma ofAnalyticOnNhd_eq
  {Phi : Complex -> Complex}
  {z : Complex}
  {h boundOne boundTwo : Real}
  {U : Set Complex}
  {UOne UTwo : Set Real}
-- given
  (hUOne : IsOpen UOne)
  (hUTwo : IsOpen UTwo)
  (hzeroOne : 0 ∈ UOne)
  (hzeroTwo : 0 ∈ UTwo)
  (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
  (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
  (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
  (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
  (hmapsOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) UOne U)
  (hmapsTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) UTwo U)
  (hPhi : AnalyticOnNhd Complex Phi U)
  (hz : z ∈ U)
  (hboundOne : forall t, t ∈ UOne -> |iteratedDeriv 4 (fun s : Real => (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
  (hboundTwo : forall t, t ∈ UTwo -> |iteratedDeriv 4 (fun s : Real => (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h boundOne boundTwo := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofAnalyticOnNhd U UOne UTwo hUOne hUTwo hzeroOne hzeroTwo hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo hmapsOne hmapsTwo hPhi hz hboundOne hboundTwo

/--
[LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma ofAnalyticTensorNormOn_eq
  {Phi : Complex -> Complex}
  {z : Complex}
  {h : Real}
  {U : Set Complex}
  {UOne UTwo : Set Real}
  {M : NNReal}
-- given
  (hU : IsOpen U)
  (hUOne : IsOpen UOne)
  (hUTwo : IsOpen UTwo)
  (hzeroOne : 0 ∈ UOne)
  (hzeroTwo : 0 ∈ UTwo)
  (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
  (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
  (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
  (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
  (hmapsOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) UOne U)
  (hmapsTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) UTwo U)
  (hPhi : AnalyticOnNhd Complex Phi U)
  (hz : z ∈ U)
  (htensor : forall w, w ∈ U -> ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOn U UOne UTwo hU hUOne hUTwo hzeroOne hzeroTwo hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo hmapsOne hmapsTwo hPhi hz M htensor

/--
[LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma ofAnalyticTensorNormOnSegments_eq
  {Phi : Complex -> Complex}
  {z : Complex}
  {h : Real}
  {U : Set Complex}
  {M : NNReal}
-- given
  (hU : IsOpen U)
  (hPhi : AnalyticOnNhd Complex Phi U)
  (htensor : forall w, w ∈ U -> ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
  (hpositiveOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) (Set.uIcc 0 h) U)
  (hnegativeOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) (Set.uIcc 0 (-h)) U)
  (hpositiveTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) (Set.uIcc 0 h) U)
  (hnegativeTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) (Set.uIcc 0 (-h)) U) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments U hU hPhi M htensor hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo

/--
[LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnCompactSegments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma ofAnalyticTensorNormOnCompactSegments_eq
  {Phi : Complex -> Complex}
  {z : Complex}
  {h : Real}
  {U K : Set Complex}
  {M : NNReal}
-- given
  (hU : IsOpen U)
  (hKU : K ⊆ U)
  (hPhi : AnalyticOnNhd Complex Phi U)
  (htensor : forall w, w ∈ K -> ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
  (hpositiveOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) (Set.uIcc 0 h) K)
  (hnegativeOne : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 + Complex.I)) (Set.uIcc 0 (-h)) K)
  (hpositiveTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) (Set.uIcc 0 h) K)
  (hnegativeTwo : Set.MapsTo (fun t : Real => z + (t : Complex) * (1 - Complex.I)) (Set.uIcc 0 (-h)) K) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnCompactSegments U K hU hKU hPhi M htensor hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo

/--
[LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnConvex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma ofAnalyticTensorNormOnConvex_eq
  {Phi : Complex -> Complex}
  {z : Complex}
  {h : Real}
  {U : Set Complex}
  {M : NNReal}
-- given
  (hUOpen : IsOpen U)
  (hUConvex : Convex Real U)
  (hPhi : AnalyticOnNhd Complex Phi U)
  (htensor : forall w, w ∈ U -> ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
  (hz : z ∈ U)
  (hpositiveOne : z + (h : Complex) * (1 + Complex.I) ∈ U)
  (hnegativeOne : z + ((-h : Real) : Complex) * (1 + Complex.I) ∈ U)
  (hpositiveTwo : z + (h : Complex) * (1 - Complex.I) ∈ U)
  (hnegativeTwo : z + ((-h : Real) : Complex) * (1 - Complex.I) ∈ U) :
-- imply
  LocalDiagonalFourthOrderAnalyticData Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnConvex U hUOpen hUConvex hPhi M htensor hz hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo

/--
[PhysicalEndpointSegmentFourthOrderBulkData.vertexLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma vertexLaplacian_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {H : PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
  (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0)
  (hendpoint : Not (vertexMarkedEndpointLayer (N k) (radius k) (some x))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y => (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x| <= (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointSegmentFourthOrderBulkData.vertexLaplacian H k x hfixed hghost hendpoint

/--
[PhysicalEndpointSegmentFourthOrderBulkData.faceLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma faceLaplacian_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {H : PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
  (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0)
  (hendpoint : Not (faceMarkedEndpointLayer (N k) (radius k) (some c))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d => (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c| <= (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointSegmentFourthOrderBulkData.faceLaplacian H k c hfixed hghost hendpoint

/--
[PhysicalEndpointLocalizedRobinInputs.ofLocalizedSegmentFourthOrderAndRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean)
-/
@[path]
private lemma ofLocalizedSegmentFourthOrderAndRange_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {Hfourth : PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius}
-- given
  (layerRate : Nat -> Real)
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hlayer_nonneg : forall k, 0 <= layerRate k)
  (hvertexFixed : forall k x, fkIsingSquareFullVertexFixedBoundary (N k) x -> (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
  (hfaceFixed : forall k c, fkIsingSquareFullFaceFixedBoundary (N k) c -> (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
  (hvertexFree : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (N k) x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x -> (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
  (hfaceFree : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (N k) c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c -> (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
  (hvertexLayer : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (N k) x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x -> Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) -> |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y => (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x| <= layerRate k)
  (hfaceLayer : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (N k) c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c -> Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) -> |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d => (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c| <= layerRate k)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
  (hscaledFourth_tendsto : Tendsto (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
  (hlayer_tendsto : Tendsto layerRate atTop (nhds 0))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12) layerRate (fun _ => 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedRobinInputs.ofLocalizedSegmentFourthOrderAndRange layerRate Hfourth hmesh_nonneg hlayer_nonneg hvertexFixed hfaceFixed hvertexFree hfaceFree hvertexLayer hfaceLayer hvertexRange hfaceRange hscaledFourth_tendsto hlayer_tendsto hmesh_tendsto


-- created on 2026-10-23
