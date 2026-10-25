import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part4
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[diagonalSegment_mapsTo_cthickening](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma diagonalSegment_mapsTo_cthickening_eq
  {K : Set Complex}
  {epsilon : Real}
  {z : Complex}
  {sgn : Bool}
-- given
  (hz : z ∈ K)
  (h : Real)
  (hmesh : 2 * |h| ≤ epsilon) :
-- imply
  Set.MapsTo (fun t : Real => z + (t : Complex) * (if sgn then 1 + Complex.I else 1 - Complex.I)) (Set.uIcc 0 h) (Metric.cthickening epsilon K) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.diagonalSegment_mapsTo_cthickening K epsilon z hz h hmesh sgn

/--
[diagonalSegment_mapsTo_of_cthickening](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma diagonalSegment_mapsTo_of_cthickening_eq
  {U K : Set Complex}
  {epsilon : Real}
  {z : Complex}
  {sgn : Bool}
-- given
  (hKU : Metric.cthickening epsilon K ⊆ U)
  (hz : z ∈ K)
  (h : Real)
  (hmesh : 2 * |h| ≤ epsilon) :
-- imply
  Set.MapsTo (fun t : Real => z + (t : Complex) * (if sgn then 1 + Complex.I else 1 - Complex.I)) (Set.uIcc 0 h) U := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.diagonalSegment_mapsTo_of_cthickening U K epsilon hKU z hz h hmesh sgn

/--
[exists_positive_compactAnalyticCollar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma exists_positive_compactAnalyticCollar_eq
  {U K : Set Complex}
-- given
  (hU : IsOpen U)
  (hK : IsCompact K)
  (hKU : K ⊆ U) :
-- imply
  ∃ epsilon : Real, 0 < epsilon ∧ Metric.cthickening epsilon K ⊆ U := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.exists_positive_compactAnalyticCollar U K hU hK hKU

/--
[exists_shift_two_abs_mesh_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma exists_shift_two_abs_mesh_le_eq
  {epsilon : Real}
-- given
  (mesh : Nat -> Real)
  (hmesh : Tendsto mesh atTop (nhds 0))
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ k0 : Nat, forall k, 2 * := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.exists_shift_two_abs_mesh_le mesh hmesh epsilon hepsilon

/--
[exists_fderiv_im_norm_bound_on_compact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma exists_fderiv_im_norm_bound_on_compact_eq
  {U K : Set Complex}
-- given
  (Phi : Complex -> Complex)
  (hU : IsOpen U)
  (hK : IsCompact K)
  (hKU : K ⊆ U)
  (hPhi : AnalyticOnNhd Complex Phi U) :
-- imply
  ∃ L : NNReal, forall w, w ∈ K -> ‖fderiv Real (fun z => (Phi z).im) w‖ ≤ L := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.exists_fderiv_im_norm_bound_on_compact Phi U K hU hK hKU hPhi

/--
[PhysicalStripMapTraceRangeData.vertexRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma vertexRange_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {H : PhysicalStripMapTraceRangeData N Phi mesh}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)} :
-- imply
  0 ≤ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im ∧ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im ≤ 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalStripMapTraceRangeData.vertexRange H k x

/--
[PhysicalStripMapTraceRangeData.faceRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma faceRange_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {H : PhysicalStripMapTraceRangeData N Phi mesh}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)} :
-- imply
  0 ≤ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im ∧ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im ≤ 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalStripMapTraceRangeData.faceRange H k c

/--
[PhysicalStripMapTraceRangeData.vertexFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma vertexFixed_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {H : PhysicalStripMapTraceRangeData N Phi mesh}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hx : fkIsingSquareFullVertexFixedBoundary (N k) x) :
-- imply
  (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalStripMapTraceRangeData.vertexFixed H k x hx

/--
[PhysicalStripMapTraceRangeData.faceFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma faceFixed_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {H : PhysicalStripMapTraceRangeData N Phi mesh}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hc : fkIsingSquareFullFaceFixedBoundary (N k) c) :
-- imply
  (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalStripMapTraceRangeData.faceFixed H k c hc

/--
[PhysicalStripMapTraceRangeData.vertexFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma vertexFree_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {H : PhysicalStripMapTraceRangeData N Phi mesh}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
  (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) :
-- imply
  (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalStripMapTraceRangeData.vertexFree H k x hfixed hghost

/--
[PhysicalStripMapTraceRangeData.faceFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma faceFree_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {H : PhysicalStripMapTraceRangeData N Phi mesh}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
  (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) :
-- imply
  (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalStripMapTraceRangeData.faceFree H k c hfixed hghost

/--
[PhysicalEndpointLocalizedRobinInputs.ofSegmentLayerAndStripMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean)
-/
@[path]
private lemma ofSegmentLayerAndStripMap_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {Hfourth : PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius}
  {Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius}
  {Hstrip : PhysicalStripMapTraceRangeData N Phi mesh}
-- given
  (hmesh_nonneg : forall k, 0 ≤ mesh k)
  (hscaledFourth_tendsto : Tendsto (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12) (fun k => 4 * Hlayer.constant * mesh k) (fun _ => 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedRobinInputs.ofSegmentLayerAndStripMap Hfourth Hlayer Hstrip hmesh_nonneg hscaledFourth_tendsto hmesh_tendsto


-- created on 2026-10-23
