import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerGreen
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[faceRobinColumnCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceRobinColumnCap_nonneg_eq
  {n : Nat}
  {source c : FKIsingSquareFullFaceNode n} :
-- imply
  0 <= faceRobinColumnCap source c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceRobinColumnCap_nonneg source c

/--
[faceBottomRowCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceBottomRowCap_nonneg_eq
  {n : Nat}
  {source c : FKIsingSquareFullFaceNode n} :
-- imply
  0 <= faceBottomRowCap source c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBottomRowCap_nonneg source c

/--
[faceMarkedEndpointLayer_coordinate_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceMarkedEndpointLayer_coordinate_cases_eq
  {n radius : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hc : faceMarkedEndpointLayer n radius (some c)) :
-- imply
  c.1.1 + c.2.1 <= radius \/ c.1.1 + (2 * n - 1 - c.2.1) <= radius := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointLayer_coordinate_cases n radius c hc

/--
[faceRobinColumnCap_modifiedLaplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceRobinColumnCap_modifiedLaplacian_nonpos_eq
  {n : Nat}
  {source c : FKIsingSquareFullFaceNode n}
-- given
  (hsource : 0 < source.1.1)
  (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (faceRobinColumnCap source) c - isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * faceRobinColumnCap source c <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceRobinColumnCap_modifiedLaplacian_nonpos n source c hsource hc

/--
[faceBottomRowCap_laplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceBottomRowCap_laplacian_nonpos_eq
  {n : Nat}
  {source c : FKIsingSquareFullFaceNode n}
-- given
  (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (faceBottomRowCap source) c <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBottomRowCap_laplacian_nonpos n source c hc

/--
[faceRobinColumnCap_modifiedLaplacian_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceRobinColumnCap_modifiedLaplacian_source_eq
  {n : Nat}
  {source : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
  (hleft : 0 < source.1.1) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (faceRobinColumnCap source) source - isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) source * faceRobinColumnCap source source = -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceRobinColumnCap_modifiedLaplacian_source n source hfixed hleft

/--
[faceBottomRowCap_laplacian_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceBottomRowCap_laplacian_source_eq
  {n : Nat}
  {source : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (faceBottomRowCap source) source = -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBottomRowCap_laplacian_source n source hfixed

/--
[faceCornerCaps_edgewise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceCornerCaps_edgewise_eq
  {n : Nat}
  {source x y : FKIsingSquareFullFaceNode n}
-- given
  (hxy : (fkIsingSquareFullFaceGraph n).Adj x y) :
-- imply
  (faceRobinColumnCap source y - faceRobinColumnCap source x) * (faceBottomRowCap source y - faceBottomRowCap source x) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceCornerCaps_edgewise n source x y hxy

/--
[facePointPoissonBarrier_le_lowerLeftProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma facePointPoissonBarrier_le_lowerLeftProduct_eq
  {n : Nat}
  {source x : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
  (hleft : 0 < source.1.1) :
-- imply
  facePointPoissonBarrier n (some source) (some x) <= faceRobinColumnCap source x * faceBottomRowCap source x / (faceRobinColumnCap source source + faceBottomRowCap source source) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePointPoissonBarrier_le_lowerLeftProduct n source x hfixed hleft

/--
[facePointPoissonBarrier_le_lowerLeftRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma facePointPoissonBarrier_le_lowerLeftRadius_eq
  {n radius : Nat}
  {distance : Real}
  {source x : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
  (hleft : 0 < source.1.1)
  (hcorner : x.1.1 + x.2.1 <= radius)
  (hdistance : 0 < distance)
  (hsourceDistance : distance <= (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient + (source.2.1 : Real)) :
-- imply
  facePointPoissonBarrier n (some source) (some x) <= ((radius : Real) + 1 / isingFermionicGhostCoefficient) * (radius : Real) / distance := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePointPoissonBarrier_le_lowerLeftRadius n radius distance source x hfixed hleft hcorner hdistance hsourceDistance

/--
[faceTopRowCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceTopRowCap_nonneg_eq
  {n : Nat}
  {source c : FKIsingSquareFullFaceNode n} :
-- imply
  0 <= faceTopRowCap n source c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceTopRowCap_nonneg n source c

/--
[faceTopRowCap_laplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceTopRowCap_laplacian_nonpos_eq
  {n : Nat}
  {source c : FKIsingSquareFullFaceNode n}
-- given
  (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (faceTopRowCap n source) c <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceTopRowCap_laplacian_nonpos n source c hc

/--
[faceTopRowCap_laplacian_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceTopRowCap_laplacian_source_eq
  {n : Nat}
  {source : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (faceTopRowCap n source) source = -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceTopRowCap_laplacian_source n source hfixed

/--
[faceUpperCornerCaps_edgewise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma faceUpperCornerCaps_edgewise_eq
  {n : Nat}
  {source x y : FKIsingSquareFullFaceNode n}
-- given
  (hxy : (fkIsingSquareFullFaceGraph n).Adj x y) :
-- imply
  (faceRobinColumnCap source y - faceRobinColumnCap source x) * (faceTopRowCap n source y - faceTopRowCap n source x) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceUpperCornerCaps_edgewise n source x y hxy

/--
[facePointPoissonBarrier_le_upperLeftProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma facePointPoissonBarrier_le_upperLeftProduct_eq
  {n : Nat}
  {source x : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
  (hleft : 0 < source.1.1) :
-- imply
  facePointPoissonBarrier n (some source) (some x) <= faceRobinColumnCap source x * faceTopRowCap n source x / (faceRobinColumnCap source source + faceTopRowCap n source source) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePointPoissonBarrier_le_upperLeftProduct n source x hfixed hleft

/--
[facePointPoissonBarrier_le_upperLeftRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma facePointPoissonBarrier_le_upperLeftRadius_eq
  {n radius : Nat}
  {distance : Real}
  {source x : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
  (hleft : 0 < source.1.1)
  (hcorner : x.1.1 + (2 * n - 1 - x.2.1) <= radius)
  (hdistance : 0 < distance)
  (hsourceDistance : distance <= (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient + (2 * n - 1 - source.2.1 : Nat)) :
-- imply
  facePointPoissonBarrier n (some source) (some x) <= ((radius : Real) + 1 / isingFermionicGhostCoefficient) * (radius : Real) / distance := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePointPoissonBarrier_le_upperLeftRadius n radius distance source x hfixed hleft hcorner hdistance hsourceDistance

/--
[facePointPoissonBarrier_le_markedEndpointRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma facePointPoissonBarrier_le_markedEndpointRadius_eq
  {n radius : Nat}
  {distance : Real}
  {source x : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
  (hleft : 0 < source.1.1)
  (hx : faceMarkedEndpointLayer n radius (some x))
  (hdistance : 0 < distance)
  (hlowerDistance : distance <= (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient + (source.2.1 : Real))
  (hupperDistance : distance <= (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient + (2 * n - 1 - source.2.1 : Nat)) :
-- imply
  facePointPoissonBarrier n (some source) (some x) <= ((radius : Real) + 1 / isingFermionicGhostCoefficient) * (radius : Real) / distance := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePointPoissonBarrier_le_markedEndpointRadius n radius distance source x hfixed hleft hx hdistance hlowerDistance hupperDistance

/--
[facePointPoissonBarrier_le_exceptionalSourceRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean)
-/
@[path]
private lemma facePointPoissonBarrier_le_exceptionalSourceRadius_eq
  {n radius : Nat}
  {distance : Real}
  {source : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
  (hleft : 0 < source.1.1)
  (hdistance : 0 < distance)
  (hlowerDistance : distance <= (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient + (source.2.1 : Real))
  (hupperDistance : distance <= (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient + (2 * n - 1 - source.2.1 : Nat)) :
-- imply
  forall z, z ∈ isingFiniteWeightedInteriorExceptionalSources (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius) -> facePointPoissonBarrier n (some source) z <= ((radius : Real) + 1 / isingFermionicGhostCoefficient) * (radius : Real) / distance := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePointPoissonBarrier_le_exceptionalSourceRadius n radius distance source hfixed hleft hdistance hlowerDistance hupperDistance


-- created on 2026-10-23
