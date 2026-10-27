import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part26
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[fkIsingSquareBoundaryLayerInwardIncrement_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerInwardIncrement_le_one_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryLayerInwardIncrement n hn side k <= 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerInwardIncrement_le_one n hn side k

/--
[markedB_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma markedB_base_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareMarkedB n) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.markedB_base n hn

/--
[vertex_eq_of_common_face_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_eq_of_common_face_increment_eq_eq
  {n : Nat}
  {e f : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n)
  (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e = fkIsingSquareFullFaceOfRadialIncidence n hn f)
  (hinc : fkIsingSquareBoundaryLayerRadialIncrement n hn e = fkIsingSquareBoundaryLayerRadialIncrement n hn f) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn f) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_eq_of_common_face_increment_eq n hn e f hface hinc

/--
[face_eq_of_common_vertex_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma face_eq_of_common_vertex_increment_eq_eq
  {n : Nat}
  {e f : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n)
  (hvertex : fkIsingSquareInteriorRadialEndpoint n hn e = fkIsingSquareInteriorRadialEndpoint n hn f)
  (hinc : fkIsingSquareBoundaryLayerRadialIncrement n hn e = fkIsingSquareBoundaryLayerRadialIncrement n hn f) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn f) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_eq_of_common_vertex_increment_eq n hn e f hvertex hinc

/--
[boundaryLayerEndpoint_directedTangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma boundaryLayerEndpoint_directedTangent_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerEndpointSide side)) = fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda ^ 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryLayerEndpoint_directedTangent n hn side k

/--
[boundaryVertexFermion_projection_inward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma boundaryVertexFermion_projection_inward_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side))) (fkIsingSquareBoundaryLayerVertexFermion n hn side k) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryVertexFermion_projection_inward n hn side k

/--
[boundaryVertexFermion_projection_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma boundaryVertexFermion_projection_endpoint_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerEndpointSide side))) (fkIsingSquareBoundaryLayerVertexFermion n hn side k) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerEndpointSide side)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryVertexFermion_projection_endpoint n hn side k

/--
[fkIsingSquareBoundaryLayerComplementInward_directedTangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerComplementInward_directedTangent_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side)) = match side with := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareBoundaryLayerComplementInward_directedTangent n hn side k

/--
[boundaryLayerComplementEndpoint_directedTangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma boundaryLayerComplementEndpoint_directedTangent_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementEndpointSide side)) = fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side)) * isingLambda ^ 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryLayerComplementEndpoint_directedTangent n hn side k

/--
[complementBoundaryVertexFermion_projection_inward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma complementBoundaryVertexFermion_projection_inward_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side))) (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.complementBoundaryVertexFermion_projection_inward n hn side k

/--
[complementBoundaryVertexFermion_projection_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma complementBoundaryVertexFermion_projection_endpoint_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementEndpointSide side))) (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementEndpointSide side)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.complementBoundaryVertexFermion_projection_endpoint n hn side k

/--
[fkIsingSquareBoundaryLayerComplementVertexFermion_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerComplementVertexFermion_normSq_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  Complex.normSq (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) = isingFermionicBoundaryVertexNormSqFactor * fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareBoundaryLayerComplementVertexFermion_normSq n hn side k

/--
[fkIsingSquareBoundaryLayerComplement_halfDiagonal_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerComplement_halfDiagonal_normSq_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  Real.sqrt 2 / 2 * Complex.normSq (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) = isingFermionicGhostCoefficient * fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareBoundaryLayerComplement_halfDiagonal_normSq n hn side k

/--
[fkIsingSquareBottomBoundaryMedialObservable_projection_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareBottomBoundaryMedialObservable_projection_west_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  isingProj 1 (fkIsingSquareBottomBoundaryMedialObservable n hn k) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .bottom k, .west)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareBottomBoundaryMedialObservable_projection_west n hn k

/--
[fkIsingSquareBottomBoundaryMedialObservable_projection_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareBottomBoundaryMedialObservable_projection_north_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  isingProj (-Complex.I) (fkIsingSquareBottomBoundaryMedialObservable n hn k) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .bottom k, .north)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareBottomBoundaryMedialObservable_projection_north n hn k

/--
[fkIsingSquareRightBoundaryMedialObservable_projection_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareRightBoundaryMedialObservable_projection_north_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  isingProj (-1) (fkIsingSquareRightBoundaryMedialObservable n hn k) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .right k, .north)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareRightBoundaryMedialObservable_projection_north n hn k

/--
[fkIsingSquareRightBoundaryMedialObservable_projection_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareRightBoundaryMedialObservable_projection_west_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  isingProj (-Complex.I) (fkIsingSquareRightBoundaryMedialObservable n hn k) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .right k, .west)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareRightBoundaryMedialObservable_projection_west n hn k

/--
[fkIsingSquareTopBoundaryMedialObservable_projection_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareTopBoundaryMedialObservable_projection_south_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  isingProj Complex.I (fkIsingSquareTopBoundaryMedialObservable n hn k) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .top k, .south)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareTopBoundaryMedialObservable_projection_south n hn k

/--
[fkIsingSquareTopBoundaryMedialObservable_projection_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareTopBoundaryMedialObservable_projection_east_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  isingProj (-1) (fkIsingSquareTopBoundaryMedialObservable n hn k) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .top k, .east)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareTopBoundaryMedialObservable_projection_east n hn k

/--
[fkIsingSquareBottomBoundaryMissingSouthObservable_projection_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareBottomBoundaryMissingSouthObservable_projection_east_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ isingProj Complex.I (fkIsingSquareBottomBoundaryMissingSouthObservable n hn k) = isingProj Complex.I (fkIsingSquareBottomBoundaryMedialObservable n hn k1) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareBottomBoundaryMissingSouthObservable_projection_east n hn k

/--
[fkIsingSquareBottomBoundaryMissingSouthObservable_projection_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareBottomBoundaryMissingSouthObservable_projection_west_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ isingProj (-1) (fkIsingSquareBottomBoundaryMissingSouthObservable n hn k) = isingProj (-1) (fkIsingSquareBottomBoundaryMedialObservable n hn k0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareBottomBoundaryMissingSouthObservable_projection_west n hn k

/--
[fkIsingSquareBottomBoundaryObservable_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma fkIsingSquareBottomBoundaryObservable_quad_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.bottom, k1) let hnorth : fkIsingSquareDirectionAvailable n x .north := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn IsingSquareSHolomorphicQuad (fkIsingSquareBottomBoundaryMissingSouthObservable n hn k) (fkIsingSquareBottomBoundaryMedialObservable n hn k0) (fkIsingSquareBoundaryFullMedialObservable n hn (fullVertexNorthEdge n x hnorth)) (fkIsingSquareBottomBoundaryMedialObservable n hn k1) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareBottomBoundaryObservable_quad n hn k

/--
[bottomBoundaryCrossDart_bondPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomBoundaryCrossDart_bondPhase_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondPhase n hn (bottomBoundaryCrossDart n k) = isingLambda := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomBoundaryCrossDart_bondPhase n hn k

/--
[bottom_boundary_inward_observable_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottom_boundary_inward_observable_phase_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn D.fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) = -isingLambda * D.fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottom_boundary_inward_observable_phase n hn k

/--
[isingPrimalProjectionDivergenceWithoutSouth_bottom_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergenceWithoutSouth_bottom_decomposition_eq
  {north east west : Complex}
-- given
  (hNE : isingProj 1 north = isingProj 1 east)
  (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
  (hphase : isingProj (-Complex.I) north = -isingLambda * isingProj 1 north) :
-- imply
  isingPrimalProjectionDivergenceWithoutSouth north east west + isingFermionicGhostCoefficient * Complex.normSq (isingProj 1 north) = -2 * Complex.normSq (isingProj 1 north) - Complex.normSq (isingProj (-Complex.I) east) - Complex.normSq (isingProj 1 west) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergenceWithoutSouth_bottom_decomposition north east west hNE hWN hphase

/--
[isingPrimalProjectionDivergenceWithoutSouth_bottom_add_ghost_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergenceWithoutSouth_bottom_add_ghost_nonpos_eq
  {north east west : Complex}
-- given
  (hNE : isingProj 1 north = isingProj 1 east)
  (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
  (hphase : isingProj (-Complex.I) north = -isingLambda * isingProj 1 north) :
-- imply
  isingPrimalProjectionDivergenceWithoutSouth north east west + isingFermionicGhostCoefficient * Complex.normSq (isingProj 1 north) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergenceWithoutSouth_bottom_add_ghost_nonpos north east west hNE hWN hphase

/--
[isingPrimalProjectionDivergenceWithoutEast_right_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergenceWithoutEast_right_decomposition_eq
  {north south west : Complex}
-- given
  (hSW : isingProj (-1) south = isingProj (-1) west)
  (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
  (hphase : isingProj (-1) west = -isingLambda * isingProj (-Complex.I) west) :
-- imply
  isingPrimalProjectionDivergenceWithoutEast north south west + isingFermionicGhostCoefficient * Complex.normSq (isingProj (-Complex.I) west) = -2 * Complex.normSq (isingProj (-Complex.I) west) - Complex.normSq (isingProj (-1) north) - Complex.normSq (isingProj (-Complex.I) south) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergenceWithoutEast_right_decomposition north south west hSW hWN hphase

/--
[isingPrimalProjectionDivergenceWithoutEast_right_add_ghost_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergenceWithoutEast_right_add_ghost_nonpos_eq
  {north south west : Complex}
-- given
  (hSW : isingProj (-1) south = isingProj (-1) west)
  (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
  (hphase : isingProj (-1) west = -isingLambda * isingProj (-Complex.I) west) :
-- imply
  isingPrimalProjectionDivergenceWithoutEast north south west + isingFermionicGhostCoefficient * Complex.normSq (isingProj (-Complex.I) west) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergenceWithoutEast_right_add_ghost_nonpos north south west hSW hWN hphase

/--
[isingPrimalProjectionDivergenceWithoutNorth_top_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergenceWithoutNorth_top_decomposition_eq
  {east south west : Complex}
-- given
  (hES : isingProj Complex.I east = isingProj Complex.I south)
  (hSW : isingProj (-1) south = isingProj (-1) west)
  (hphase : isingProj Complex.I south = -isingLambda * isingProj (-1) south) :
-- imply
  isingPrimalProjectionDivergenceWithoutNorth east south west + isingFermionicGhostCoefficient * Complex.normSq (isingProj (-1) south) = -2 * Complex.normSq (isingProj (-1) south) - Complex.normSq (isingProj (-1) east) - Complex.normSq (isingProj Complex.I west) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergenceWithoutNorth_top_decomposition east south west hES hSW hphase

/--
[isingPrimalProjectionDivergenceWithoutNorth_top_add_ghost_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergenceWithoutNorth_top_add_ghost_nonpos_eq
  {east south west : Complex}
-- given
  (hES : isingProj Complex.I east = isingProj Complex.I south)
  (hSW : isingProj (-1) south = isingProj (-1) west)
  (hphase : isingProj Complex.I south = -isingLambda * isingProj (-1) south) :
-- imply
  isingPrimalProjectionDivergenceWithoutNorth east south west + isingFermionicGhostCoefficient * Complex.normSq (isingProj (-1) south) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergenceWithoutNorth_top_add_ghost_nonpos east south west hES hSW hphase

/--
[isingPrimalProjectionDivergence_bottomRightCorner_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergence_bottomRightCorner_decomposition_eq
  {north west : Complex}
-- given
  (hbottom : isingProj (-Complex.I) north = -isingLambda * isingProj 1 north)
  (hright : isingProj (-1) west = -isingLambda * isingProj (-Complex.I) west) :
-- imply
  (Complex.normSq (isingProj (-Complex.I) north) - Complex.normSq (isingProj (-1) north)) + (Complex.normSq (isingProj (-1) west) - Complex.normSq (isingProj Complex.I west)) + isingFermionicGhostCoefficient * (Complex.normSq (isingProj 1 north) + Complex.normSq (isingProj (-Complex.I) west)) = -4 * (Complex.normSq (isingProj 1 north) + Complex.normSq (isingProj (-Complex.I) west)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergence_bottomRightCorner_decomposition north west hbottom hright

/--
[isingPrimalProjectionDivergence_bottomRightCorner_add_ghost_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergence_bottomRightCorner_add_ghost_nonpos_eq
  {north west : Complex}
-- given
  (hbottom : isingProj (-Complex.I) north = -isingLambda * isingProj 1 north)
  (hright : isingProj (-1) west = -isingLambda * isingProj (-Complex.I) west) :
-- imply
  (Complex.normSq (isingProj (-Complex.I) north) - Complex.normSq (isingProj (-1) north)) + (Complex.normSq (isingProj (-1) west) - Complex.normSq (isingProj Complex.I west)) + isingFermionicGhostCoefficient * (Complex.normSq (isingProj 1 north) + Complex.normSq (isingProj (-Complex.I) west)) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergence_bottomRightCorner_add_ghost_nonpos north west hbottom hright

/--
[isingPrimalProjectionDivergence_topRightCorner_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergence_topRightCorner_decomposition_eq
  {south west : Complex}
-- given
  (htop : isingProj Complex.I south = -isingLambda * isingProj (-1) south)
  (hright : isingProj (-1) west = -isingLambda * isingProj (-Complex.I) west) :
-- imply
  (Complex.normSq (isingProj Complex.I south) - Complex.normSq (isingProj 1 south)) + (Complex.normSq (isingProj (-1) west) - Complex.normSq (isingProj Complex.I west)) + isingFermionicGhostCoefficient * (Complex.normSq (isingProj (-1) south) + Complex.normSq (isingProj (-Complex.I) west)) = -4 * (Complex.normSq (isingProj (-1) south) + Complex.normSq (isingProj (-Complex.I) west)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergence_topRightCorner_decomposition south west htop hright

/--
[isingPrimalProjectionDivergence_topRightCorner_add_ghost_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergence_topRightCorner_add_ghost_nonpos_eq
  {south west : Complex}
-- given
  (htop : isingProj Complex.I south = -isingLambda * isingProj (-1) south)
  (hright : isingProj (-1) west = -isingLambda * isingProj (-Complex.I) west) :
-- imply
  (Complex.normSq (isingProj Complex.I south) - Complex.normSq (isingProj 1 south)) + (Complex.normSq (isingProj (-1) west) - Complex.normSq (isingProj Complex.I west)) + isingFermionicGhostCoefficient * (Complex.normSq (isingProj (-1) south) + Complex.normSq (isingProj (-Complex.I) west)) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergence_topRightCorner_add_ghost_nonpos south west htop hright

/--
[isingPrimalProjectionDivergenceWithoutWest_left_add_ghost_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergenceWithoutWest_left_add_ghost_nonneg_eq
  {north east south : Complex}
-- given
  (hNE : isingProj (-1) north = isingProj (-1) east)
  (hES : isingProj (-Complex.I) east = isingProj (-Complex.I) south)
  (hphase : isingProj 1 south = isingLambda * isingProj Complex.I north) :
-- imply
  0 ≤ isingPrimalProjectionDivergenceWithoutWest north east south - isingFermionicGhostCoefficient * Complex.normSq (isingProj Complex.I north) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingPrimalProjectionDivergenceWithoutWest_left_add_ghost_nonneg north east south hNE hES hphase

/--
[left_boundary_interior_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma left_boundary_interior_increment_eq_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryLayerRadialIncrement n hn (Quot.mk _ (leftInteriorEastDart n hn k)) = fkIsingSquareBoundaryLayerRadialIncrement n hn (Quot.mk _ (leftInteriorSouthDart n hn k)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.left_boundary_interior_increment_eq n hn k

/--
[left_boundary_endpoint_observable_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma left_boundary_endpoint_observable_phase_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  let e := fkIsingSquareLeftVerticalEdge n hn k let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn D.fermionicObservable (.dart (e, .south)) = isingLambda * D.fermionicObservable (.dart (e, .east)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.left_boundary_endpoint_observable_phase n hn k

/--
[wiredArc_vertex_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma wiredArc_vertex_step_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareLeftVerticalLower n hn k) = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareLeftVerticalUpper n hn k) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.wiredArc_vertex_step n hn k

/--
[vertex_fixedBoundary_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_fixedBoundary_eq_zero_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hx : fkIsingSquareFullVertexFixedBoundary n x) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_fixedBoundary_eq_zero n hn x hx

/--
[vertex_fixedBoundary_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_fixedBoundary_nonneg_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hx : fkIsingSquareFullVertexFixedBoundary n x) :
-- imply
  0 <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_fixedBoundary_nonneg n hn x hx

/--
[bottom_boundary_transverse_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottom_boundary_transverse_increment_eq_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.bottom, k1) let hx : fkIsingSquareDirectionAvailable n x .north := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn let e := fkIsingSquareDirectionEdge n x .north hx fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottom_boundary_transverse_increment_eq n hn k

/--
[bottom_boundary_vertex_difference_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottom_boundary_vertex_difference_west_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x0 := fkIsingSquareBoundaryVertex n (.bottom, k0) let x1 := fkIsingSquareBoundaryVertex n (.bottom, k1) let e := fkIsingSquarePerimeterEdge n .bottom k0 (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottom_boundary_vertex_difference_west n hn k

/--
[bottom_boundary_vertex_laplacian_eq_increment_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottom_boundary_vertex_laplacian_eq_increment_divergence_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.bottom, k1) let he : fkIsingSquareDirectionAvailable n x .east := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] omega let hnorth : fkIsingSquareDirectionAvailable n x .north := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn let hw : fkIsingSquareDirectionAvailable n x .west := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] let eE := fullVertexEastEdge n x he let eN := fullVertexNorthEdge n x hnorth let eW := fullVertexWestEdge n x hw isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) + (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) + (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .north)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .west))) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottom_boundary_vertex_laplacian_eq_increment_divergence n hn k

/--
[bottom_boundary_vertex_laplacian_eq_projectionDivergenceWithoutSouth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottom_boundary_vertex_laplacian_eq_projectionDivergenceWithoutSouth_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.bottom, k1) let hnorth : fkIsingSquareDirectionAvailable n x .north := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn let eN := fullVertexNorthEdge n x hnorth isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = isingPrimalProjectionDivergenceWithoutSouth (fkIsingSquareBoundaryFullMedialObservable n hn eN) (fkIsingSquareBottomBoundaryMedialObservable n hn k1) (fkIsingSquareBottomBoundaryMedialObservable n hn k0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottom_boundary_vertex_laplacian_eq_projectionDivergenceWithoutSouth n hn k

/--
[right_boundary_transverse_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma right_boundary_transverse_increment_eq_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.right, k1) let hx : fkIsingSquareDirectionAvailable n x .west := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn let e := fkIsingSquareDirectionEdge n x .west hx fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.right_boundary_transverse_increment_eq n hn k

/--
[rightBoundaryCrossDart_bondPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma rightBoundaryCrossDart_bondPhase_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondPhase n hn (rightBoundaryCrossDart n k) = isingLambda := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.rightBoundaryCrossDart_bondPhase n hn k

/--
[right_boundary_inward_observable_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma right_boundary_inward_observable_phase_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn D.fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .right k0, .north)) = -isingLambda * D.fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.right_boundary_inward_observable_phase n hn k

/--
[right_boundary_vertex_difference_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma right_boundary_vertex_difference_south_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x0 := fkIsingSquareBoundaryVertex n (.right, k0) let x1 := fkIsingSquareBoundaryVertex n (.right, k1) let e := fkIsingSquarePerimeterEdge n .right k0 (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.right_boundary_vertex_difference_south n hn k

/--
[right_boundary_projection_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma right_boundary_projection_cycle_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.right, k1) let hwest : fkIsingSquareDirectionAvailable n x .west := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn let north := fkIsingSquareRightBoundaryMedialObservable n hn k1 let south := fkIsingSquareRightBoundaryMedialObservable n hn k0 let west := fkIsingSquareBoundaryFullMedialObservable n hn (fullVertexWestEdge n x hwest) isingProj (-1) south = isingProj (-1) west ∧ isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.right_boundary_projection_cycle n hn k

/--
[right_boundary_vertex_laplacian_eq_increment_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma right_boundary_vertex_laplacian_eq_increment_divergence_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.right, k1) let hnorth : fkIsingSquareDirectionAvailable n x .north := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] omega let hsouth : fkIsingSquareDirectionAvailable n x .south := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] let hwest : fkIsingSquareDirectionAvailable n x .west := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn let eN := fullVertexNorthEdge n x hnorth let eS := fullVertexSouthEdge n x hsouth let eW := fullVertexWestEdge n x hwest isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) + (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) + (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.right_boundary_vertex_laplacian_eq_increment_divergence n hn k

/--
[right_boundary_vertex_laplacian_eq_projectionDivergenceWithoutEast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma right_boundary_vertex_laplacian_eq_projectionDivergenceWithoutEast_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.right, k1) let hwest : fkIsingSquareDirectionAvailable n x .west := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = isingPrimalProjectionDivergenceWithoutEast (fkIsingSquareRightBoundaryMedialObservable n hn k1) (fkIsingSquareRightBoundaryMedialObservable n hn k0) (fkIsingSquareBoundaryFullMedialObservable n hn (fullVertexWestEdge n x hwest)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.right_boundary_vertex_laplacian_eq_projectionDivergenceWithoutEast n hn k

/--
[top_boundary_transverse_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma top_boundary_transverse_increment_eq_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.top, k1) let hx : fkIsingSquareDirectionAvailable n x .south := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn let e := fkIsingSquareDirectionEdge n x .south hx fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.top_boundary_transverse_increment_eq n hn k

/--
[topBoundaryCrossDart_bondPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topBoundaryCrossDart_bondPhase_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondPhase n hn (topBoundaryCrossDart n k) = isingLambda := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topBoundaryCrossDart_bondPhase n hn k

/--
[top_boundary_inward_observable_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma top_boundary_inward_observable_phase_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn D.fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .top k0, .south)) = -isingLambda * D.fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.top_boundary_inward_observable_phase n hn k

/--
[top_boundary_vertex_difference_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma top_boundary_vertex_difference_east_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x0 := fkIsingSquareBoundaryVertex n (.top, k0) let x1 := fkIsingSquareBoundaryVertex n (.top, k1) let e := fkIsingSquarePerimeterEdge n .top k0 (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.top_boundary_vertex_difference_east n hn k

/--
[top_boundary_projection_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma top_boundary_projection_cycle_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.top, k1) let hsouth : fkIsingSquareDirectionAvailable n x .south := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn let east := fkIsingSquareTopBoundaryMedialObservable n hn k0 let south := fkIsingSquareBoundaryFullMedialObservable n hn (fullVertexSouthEdge n x hsouth) let west := fkIsingSquareTopBoundaryMedialObservable n hn k1 isingProj Complex.I east = isingProj Complex.I south ∧ isingProj (-1) south = isingProj (-1) west := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.top_boundary_projection_cycle n hn k

/--
[top_boundary_vertex_laplacian_eq_increment_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma top_boundary_vertex_laplacian_eq_increment_divergence_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.top, k1) let heast : fkIsingSquareDirectionAvailable n x .east := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] let hsouth : fkIsingSquareDirectionAvailable n x .south := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn let hwest : fkIsingSquareDirectionAvailable n x .west := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] omega let eE := fullVertexEastEdge n x heast let eS := fullVertexSouthEdge n x hsouth let eW := fullVertexWestEdge n x hwest isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) + (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) + (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.top_boundary_vertex_laplacian_eq_increment_divergence n hn k

/--
[top_boundary_vertex_laplacian_eq_projectionDivergenceWithoutNorth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma top_boundary_vertex_laplacian_eq_projectionDivergenceWithoutNorth_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.top, k1) let hsouth : fkIsingSquareDirectionAvailable n x .south := by simp [x, fkIsingSquareDirectionAvailable, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] exact hn isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = isingPrimalProjectionDivergenceWithoutNorth (fkIsingSquareTopBoundaryMedialObservable n hn k0) (fkIsingSquareBoundaryFullMedialObservable n hn (fullVertexSouthEdge n x hsouth)) (fkIsingSquareTopBoundaryMedialObservable n hn k1) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.top_boundary_vertex_laplacian_eq_projectionDivergenceWithoutNorth n hn k

/--
[bottom_boundary_face_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottom_boundary_face_step_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let j : Fin (2 * n) := ⟨0, by omega⟩ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (k1, j) = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (k0, j) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottom_boundary_face_step n hn k

/--
[right_boundary_face_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma right_boundary_face_step_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let i : Fin (2 * n) := ⟨2 * n - 1, by omega⟩ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i, k1) = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i, k0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.right_boundary_face_step n hn k

/--
[top_boundary_face_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma top_boundary_face_step_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let i0 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let i1 : Fin (2 * n) := ⟨k.1, by omega⟩ let j : Fin (2 * n) := ⟨2 * n - 1, by omega⟩ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i0, j) = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i1, j) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.top_boundary_face_step n hn k

/--
[boundaryLayer_terminalDart_observable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma boundaryLayer_terminalDart_observable_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryLayer_terminalDart_observable n hn

/--
[boundaryLayer_terminalDart_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma boundaryLayer_terminalDart_increment_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryLayer_terminalDart_increment n hn

/--
[terminalAdjacentFace_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma terminalAdjacentFace_eq_one_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) = 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.terminalAdjacentFace_eq_one n hn

/--
[terminalAdjacentFace_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma terminalAdjacentFace_nonneg_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  0 <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.terminalAdjacentFace_nonneg n hn

/--
[terminalAdjacentFace_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma terminalAdjacentFace_le_one_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) <= 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.terminalAdjacentFace_le_one n hn

/--
[face_fixedBoundary_eq_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma face_fixedBoundary_eq_terminal_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hc : fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_fixedBoundary_eq_terminal n hn c hc

/--
[face_fixedBoundary_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma face_fixedBoundary_eq_one_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hc : fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c = 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_fixedBoundary_eq_one n hn c hc

/--
[face_fixedBoundary_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma face_fixedBoundary_le_one_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hc : fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c <= 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_fixedBoundary_le_one n hn c hc

/--
[face_fixedBoundary_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma face_fixedBoundary_nonneg_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hc : fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  0 <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_fixedBoundary_nonneg n hn c hc

/--
[boundaryLayer_inwardIncrement_eq_terminal_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma boundaryLayer_inwardIncrement_eq_terminal_sub_vertex_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hfree : side ≠ .left) :
-- imply
  fkIsingSquareBoundaryLayerInwardIncrement n hn side k = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareBoundaryVertex n (side, k)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryLayer_inwardIncrement_eq_terminal_sub_vertex n hn side k hfree

/--
[boundaryLayer_inwardIncrement_eq_one_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma boundaryLayer_inwardIncrement_eq_one_sub_vertex_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hfree : side ≠ .left) :
-- imply
  fkIsingSquareBoundaryLayerInwardIncrement n hn side k = 1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareBoundaryVertex n (side, k)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryLayer_inwardIncrement_eq_one_sub_vertex n hn side k hfree

/--
[freeBoundary_vertex_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma freeBoundary_vertex_le_one_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hfree : side ≠ .left) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareBoundaryVertex n (side, k)) <= 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.freeBoundary_vertex_le_one n hn side k hfree

/--
[boundaryLayer_halfDiagonal_eq_ghost_terminal_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma boundaryLayer_halfDiagonal_eq_ghost_terminal_sub_vertex_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hfree : side ≠ .left) :
-- imply
  Real.sqrt 2 / 2 * Complex.normSq (fkIsingSquareBoundaryLayerVertexFermion n hn side k) = isingFermionicGhostCoefficient * ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareBoundaryVertex n (side, k))) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryLayer_halfDiagonal_eq_ghost_terminal_sub_vertex n hn side k hfree

/--
[boundaryLayer_halfDiagonal_eq_ghost_one_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma boundaryLayer_halfDiagonal_eq_ghost_one_sub_vertex_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hfree : side ≠ .left) :
-- imply
  Real.sqrt 2 / 2 * Complex.normSq (fkIsingSquareBoundaryLayerVertexFermion n hn side k) = isingFermionicGhostCoefficient * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareBoundaryVertex n (side, k))) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryLayer_halfDiagonal_eq_ghost_one_sub_vertex n hn side k hfree

/--
[bottom_boundary_complementIncrement_eq_terminal_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottom_boundary_complementIncrement_eq_terminal_sub_vertex_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .bottom k0, fkIsingSquareBoundaryLayerComplementInwardSide .bottom)) = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareBoundaryVertex n (.bottom, k1)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottom_boundary_complementIncrement_eq_terminal_sub_vertex n hn k

/--
[bottom_boundary_complement_halfDiagonal_eq_ghost_terminal_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottom_boundary_complement_halfDiagonal_eq_ghost_terminal_sub_vertex_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ Real.sqrt 2 / 2 * Complex.normSq (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .bottom k0) = isingFermionicGhostCoefficient * ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareBoundaryVertex n (.bottom, k1))) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottom_boundary_complement_halfDiagonal_eq_ghost_terminal_sub_vertex n hn k

/--
[bottom_boundary_complement_halfDiagonal_eq_ghost_one_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottom_boundary_complement_halfDiagonal_eq_ghost_one_sub_vertex_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩ let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ Real.sqrt 2 / 2 * Complex.normSq (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .bottom k0) = isingFermionicGhostCoefficient * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareBoundaryVertex n (.bottom, k1))) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottom_boundary_complement_halfDiagonal_eq_ghost_one_sub_vertex n hn k

/--
[bottomRightCorner_inward_observable_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCorner_inward_observable_eq_zero_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn), .west)) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCorner_inward_observable_eq_zero n hn

/--
[bottomRightCorner_inward_increment_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCorner_inward_increment_eq_zero_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn), .west)) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCorner_inward_increment_eq_zero n hn

/--
[bottomRightCornerCrossDart_bondPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCornerCrossDart_bondPhase_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondPhase n hn (bottomRightCornerCrossDart n hn) = Complex.I := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCornerCrossDart_bondPhase n hn

/--
[bottomRightCorner_inward_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCorner_inward_increment_eq_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .bottom (bottomRightCornerLast n hn), .north)) = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn), .west)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCorner_inward_increment_eq n hn

/--
[bottomRightCorner_vertex_difference_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCorner_vertex_difference_west_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let last := bottomRightCornerLast n hn let zero := bottomRightCornerZero n hn let x0 := fkIsingSquareBoundaryVertex n (.bottom, last) let x1 := fkIsingSquareBoundaryVertex n (.right, zero) let e := fkIsingSquarePerimeterEdge n .bottom last (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCorner_vertex_difference_west n hn

/--
[bottomRightCorner_vertex_laplacian_eq_increment_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCorner_vertex_laplacian_eq_increment_divergence_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let last := bottomRightCornerLast n hn let zero := bottomRightCornerZero n hn let x := fkIsingSquareBoundaryVertex n (.right, zero) let eN := fkIsingSquarePerimeterEdge n .right zero let eW := fkIsingSquarePerimeterEdge n .bottom last isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) + (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .north)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .west))) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCorner_vertex_laplacian_eq_increment_divergence n hn

/--
[bottomRightCorner_vertex_laplacian_eq_corner_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCorner_vertex_laplacian_eq_corner_divergence_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let last := bottomRightCornerLast n hn let zero := bottomRightCornerZero n hn let x := fkIsingSquareBoundaryVertex n (.right, zero) let a := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west)) let b := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right zero, .west)) let d := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right zero, .north)) isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = (b - d) + (b - a) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCorner_vertex_laplacian_eq_corner_divergence n hn

/--
[vertex_modifiedLaplacian_nonpos_of_bottomRightCorner_of_increment_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_modifiedLaplacian_nonpos_of_bottomRightCorner_of_increment_bound_eq
  {n : Nat}
-- given
  (hn : 0 < n)
  (hcorner : let last := bottomRightCornerLast n hn let zero := bottomRightCornerZero n hn let a := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west)) let b := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right zero, .west)) let d := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right zero, .north)) 2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d) :
-- imply
  let zero := bottomRightCornerZero n hn let x := fkIsingSquareBoundaryVertex n (.right, zero) isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_modifiedLaplacian_nonpos_of_bottomRightCorner_of_increment_bound n hn hcorner

/--
[bottomRightCorner_increment_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCorner_increment_bound_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let last := bottomRightCornerLast n hn let zero := bottomRightCornerZero n hn let a := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west)) let b := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right zero, .west)) let d := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right zero, .north)) 2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCorner_increment_bound n hn

/--
[vertex_modifiedLaplacian_nonpos_of_bottomRightCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_modifiedLaplacian_nonpos_of_bottomRightCorner_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let zero := bottomRightCornerZero n hn let x := fkIsingSquareBoundaryVertex n (.right, zero) isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_modifiedLaplacian_nonpos_of_bottomRightCorner n hn

/--
[bottomRightCorner_rightComplement_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCorner_rightComplement_phase_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let k0 := bottomRightCornerZero n hn isingProj (-Complex.I) (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .right k0) = -isingLambda * isingProj 1 (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .right k0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCorner_rightComplement_phase n hn

/--
[bottomRightCorner_bottomStandard_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCorner_bottomStandard_phase_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let last := bottomRightCornerLast n hn isingProj (-1) (fkIsingSquareBoundaryLayerVertexFermion n hn .bottom last) = -isingLambda * isingProj (-Complex.I) (fkIsingSquareBoundaryLayerVertexFermion n hn .bottom last) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCorner_bottomStandard_phase n hn

/--
[topRightCorner_rightStandard_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topRightCorner_rightStandard_phase_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let last := bottomRightCornerLast n hn isingProj Complex.I (fkIsingSquareBoundaryLayerVertexFermion n hn .right last) = -isingLambda * isingProj (-1) (fkIsingSquareBoundaryLayerVertexFermion n hn .right last) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topRightCorner_rightStandard_phase n hn

/--
[topRightCorner_topComplement_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topRightCorner_topComplement_phase_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let k0 := bottomRightCornerZero n hn isingProj (-1) (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .top k0) = -isingLambda * isingProj (-Complex.I) (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .top k0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topRightCorner_topComplement_phase n hn

/--
[topRightCorner_inward_observable_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topRightCorner_inward_observable_eq_zero_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn), .east)) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topRightCorner_inward_observable_eq_zero n hn

/--
[topRightCorner_inward_increment_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topRightCorner_inward_increment_eq_zero_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn), .east)) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topRightCorner_inward_increment_eq_zero n hn

/--
[topRightCorner_inward_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topRightCorner_inward_increment_eq_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right (bottomRightCornerLast n hn), .east)) = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn), .east)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topRightCorner_inward_increment_eq n hn

/--
[topRightCorner_vertex_difference_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topRightCorner_vertex_difference_south_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let last := bottomRightCornerLast n hn let zero := bottomRightCornerZero n hn let x0 := fkIsingSquareBoundaryVertex n (.right, last) let x1 := fkIsingSquareBoundaryVertex n (.top, zero) let e := fkIsingSquarePerimeterEdge n .right last (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topRightCorner_vertex_difference_south n hn

/--
[topRightCorner_vertex_laplacian_eq_increment_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topRightCorner_vertex_laplacian_eq_increment_divergence_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let last := bottomRightCornerLast n hn let zero := bottomRightCornerZero n hn let x := fkIsingSquareBoundaryVertex n (.top, zero) let eS := fkIsingSquarePerimeterEdge n .right last let eW := fkIsingSquarePerimeterEdge n .top zero isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) + (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topRightCorner_vertex_laplacian_eq_increment_divergence n hn

/--
[topRightCorner_vertex_laplacian_eq_corner_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topRightCorner_vertex_laplacian_eq_corner_divergence_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let last := bottomRightCornerLast n hn let zero := bottomRightCornerZero n hn let x := fkIsingSquareBoundaryVertex n (.top, zero) let a := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right last, .south)) let b := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .top zero, .east)) let d := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .top zero, .south)) isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = (b - a) + (b - d) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topRightCorner_vertex_laplacian_eq_corner_divergence n hn

/--
[vertex_modifiedLaplacian_nonpos_of_topRightCorner_of_increment_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_modifiedLaplacian_nonpos_of_topRightCorner_of_increment_bound_eq
  {n : Nat}
-- given
  (hn : 0 < n)
  (hcorner : let last := bottomRightCornerLast n hn let zero := bottomRightCornerZero n hn let a := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right last, .south)) let b := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .top zero, .east)) let d := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .top zero, .south)) 2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d) :
-- imply
  let zero := bottomRightCornerZero n hn let x := fkIsingSquareBoundaryVertex n (.top, zero) isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_modifiedLaplacian_nonpos_of_topRightCorner_of_increment_bound n hn hcorner

/--
[topRightCorner_increment_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topRightCorner_increment_bound_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let last := bottomRightCornerLast n hn let zero := bottomRightCornerZero n hn let a := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .right last, .south)) let b := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .top zero, .east)) let d := fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n .top zero, .south)) 2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topRightCorner_increment_bound n hn

/--
[vertex_modifiedLaplacian_nonpos_of_topRightCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_modifiedLaplacian_nonpos_of_topRightCorner_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  let zero := bottomRightCornerZero n hn let x := fkIsingSquareBoundaryVertex n (.top, zero) isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_modifiedLaplacian_nonpos_of_topRightCorner n hn

/--
[bottomRightCorner_ghostMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma bottomRightCorner_ghostMultiplicity_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareFullVertexGhostMultiplicity n (fkIsingSquareBoundaryVertex n (.right, bottomRightCornerZero n hn)) = 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.bottomRightCorner_ghostMultiplicity n hn

/--
[topRightCorner_ghostMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma topRightCorner_ghostMultiplicity_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareFullVertexGhostMultiplicity n (fkIsingSquareBoundaryVertex n (.top, bottomRightCornerZero n hn)) = 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.topRightCorner_ghostMultiplicity n hn

/--
[cornerIncrementDivergence_add_ghost_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma cornerIncrementDivergence_add_ghost_nonpos_eq
  {far₁ near far₂ : Real}
-- given
  (hcorner : 2 * (1 + isingFermionicGhostCoefficient) * near ≤ far₁ + far₂) :
-- imply
  (near - far₁) + (near - far₂) + 2 * isingFermionicGhostCoefficient * near ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.cornerIncrementDivergence_add_ghost_nonpos far₁ near far₂ hcorner

/--
[vertex_modifiedLaplacian_nonpos_of_bottomBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_modifiedLaplacian_nonpos_of_bottomBoundary_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.bottom, k1) isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_modifiedLaplacian_nonpos_of_bottomBoundary n hn k

/--
[vertex_modifiedLaplacian_nonpos_of_rightBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_modifiedLaplacian_nonpos_of_rightBoundary_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.right, k1) isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_modifiedLaplacian_nonpos_of_rightBoundary n hn k

/--
[vertex_modifiedLaplacian_nonpos_of_topBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_modifiedLaplacian_nonpos_of_topBoundary_eq
  {n : Nat}
  {k : Fin (2 * n - 1)}
-- given
  (hn : 0 < n) :
-- imply
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩ let x := fkIsingSquareBoundaryVertex n (.top, k1) isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_modifiedLaplacian_nonpos_of_topBoundary n hn k

/--
[vertex_modifiedLaplacian_nonpos_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_modifiedLaplacian_nonpos_of_interior_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (heast : fkIsingSquareDirectionAvailable n x .east)
  (hnorth : fkIsingSquareDirectionAvailable n x .north)
  (hwest : fkIsingSquareDirectionAvailable n x .west)
  (hsouth : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x) <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_modifiedLaplacian_nonpos_of_interior n hn x heast hnorth hwest hsouth

/--
[vertex_modifiedLaplacian_nonpos_of_not_wiredArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma vertex_modifiedLaplacian_nonpos_of_not_wiredArc_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hxFree : ¬ fkIsingSquareWiredArc n x) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x) ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_modifiedLaplacian_nonpos_of_not_wiredArc n hn x hxFree

/--
[face_modifiedLaplacian_nonneg_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma face_modifiedLaplacian_nonneg_of_interior_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (heast : c.1.1 + 1 < 2 * n)
  (hnorth : c.2.1 + 1 < 2 * n)
  (hwest : 0 < c.1.1)
  (hsouth : 0 < c.2.1) :
-- imply
  0 <= isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_modifiedLaplacian_nonneg_of_interior n hn c heast hnorth hwest hsouth

/--
[face_modifiedLaplacian_nonneg_of_leftBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma face_modifiedLaplacian_nonneg_of_leftBoundary_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hleft : c.1.1 = 0)
  (heast : c.1.1 + 1 < 2 * n)
  (hnorth : c.2.1 + 1 < 2 * n)
  (hsouth : 0 < c.2.1) :
-- imply
  0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_modifiedLaplacian_nonneg_of_leftBoundary n hn c hleft heast hnorth hsouth

/--
[face_modifiedLaplacian_nonneg_of_not_fixedBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma face_modifiedLaplacian_nonneg_of_not_fixedBoundary_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hcFree : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_modifiedLaplacian_nonneg_of_not_fixedBoundary n hn c hcFree

/--
[radialPatchPrimal_exists_orderedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma radialPatchPrimal_exists_orderedDual_eq
  {n m : Nat}
  {p : FKIsingSquareRadialPatchPrimalNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  ∃ q : FKIsingSquareRadialPatchDualNode m, radialPatchPrimalValue n m hn hm p ≤ radialPatchDualValue n m hn hm hm2 q := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimal_exists_orderedDual n m hn hm hm2 p

/--
[radialPatchDual_exists_orderedPrimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma radialPatchDual_exists_orderedPrimal_eq
  {n m : Nat}
  {q : FKIsingSquareRadialPatchDualNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  ∃ p : FKIsingSquareRadialPatchPrimalNode m, radialPatchPrimalValue n m hn hm p ≤ radialPatchDualValue n m hn hm hm2 q := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDual_exists_orderedPrimal n m hn hm hm2 q

/--
[radialPatch_unitRange_of_fullSquareGhost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean)
-/
@[path]
private lemma radialPatch_unitRange_of_fullSquareGhost_eq
  {n m : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  (∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p ∧ radialPatchPrimalValue n m hn hm p ≤ 1) ∧ (∀ q, 0 ≤ radialPatchDualValue n m hn hm hm2 q ∧ radialPatchDualValue n m hn hm hm2 q ≤ 1) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatch_unitRange_of_fullSquareGhost n m hn hm hm2


-- created on 2026-10-23
