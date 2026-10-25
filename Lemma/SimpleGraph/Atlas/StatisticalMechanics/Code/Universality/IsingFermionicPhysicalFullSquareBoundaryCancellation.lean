import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareFullIntegratedPrimitive


/--
[fkIsingSquarePerimeterInteriorRadialEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquarePerimeterInteriorRadialEndpoint_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorRadialEndpoint n hn (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k) = fkIsingSquareBoundaryVertex n (side, k) := by
-- proof
  apply StatMech.Universality.fkIsingSquarePerimeterInteriorRadialEndpoint n hn side k

/--
[fkIsingSquarePerimeterInteriorFace_fixedBoundary_of_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquarePerimeterInteriorFace_fixedBoundary_of_free_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hfree : side ≠ .left) :
-- imply
  fkIsingSquareFullFaceFixedBoundary n (fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) := by
-- proof
  apply StatMech.Universality.fkIsingSquarePerimeterInteriorFace_fixedBoundary_of_free n hn side k hfree

/--
[FKIsingSquarePerimeterOppositeCarrierSwitchingAt.paired_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma paired_summand_eq
  {n : Nat}
  {hn : 0 < n}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
  {S : FKIsingSquarePerimeterOppositeCarrierSwitchingAt n hn side k}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)} :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand (S.pairing omega) (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterCancelledSide side)) = -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega S.mate := by
-- proof
  apply StatMech.Universality.FKIsingSquarePerimeterOppositeCarrierSwitchingAt.paired_summand S omega

/--
[FKIsingSquarePerimeterOppositeCarrierSwitchingAt.observable_eq_neg_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma observable_eq_neg_mate_eq
  {n : Nat}
  {hn : 0 < n}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
  {S : FKIsingSquarePerimeterOppositeCarrierSwitchingAt n hn side k} :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterCancelledSide side)) = -(fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable S.mate := by
-- proof
  apply StatMech.Universality.FKIsingSquarePerimeterOppositeCarrierSwitchingAt.observable_eq_neg_mate S

/--
[FKIsingSquarePerimeterOppositeCarrierSwitchingAt.cancellationAt_of_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma cancellationAt_of_transport_eq
  {n : Nat}
  {hn : 0 < n}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
  {S : FKIsingSquarePerimeterOppositeCarrierSwitchingAt n hn side k}
-- given
  (htransport : (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable S.mate = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterCancelledSide side))) :
-- imply
  FKIsingSquarePerimeterCancellationAt n hn side k := by
-- proof
  apply StatMech.Universality.FKIsingSquarePerimeterOppositeCarrierSwitchingAt.cancellationAt_of_transport S htransport

/--
[FKIsingSquarePerimeterCancellationSwitchingAt.cancellationAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma cancellationAt_eq
  {n : Nat}
  {hn : 0 < n}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
  {S : FKIsingSquarePerimeterCancellationSwitchingAt n hn side k} :
-- imply
  FKIsingSquarePerimeterCancellationAt n hn side k := by
-- proof
  apply StatMech.Universality.FKIsingSquarePerimeterCancellationSwitchingAt.cancellationAt S

/--
[FKIsingSquarePerimeterGlobalPathSwitchingAt.cancellationAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma cancellationAt_eq_2
  {n : Nat}
  {hn : 0 < n}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
  {S : FKIsingSquarePerimeterGlobalPathSwitchingAt n hn side k} :
-- imply
  FKIsingSquarePerimeterCancellationAt n hn side k := by
-- proof
  apply StatMech.Universality.FKIsingSquarePerimeterGlobalPathSwitchingAt.cancellationAt S

/--
[isingF_west_ne_zero_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma isingF_west_ne_zero_of_ne_zero_eq
  {X : Complex}
-- given
  (hX : X ≠ 0) :
-- imply
  isingF 0 X ≠ 0 := by
-- proof
  apply StatMech.Universality.isingF_west_ne_zero_of_ne_zero X hX

/--
[isingF_east_ne_zero_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma isingF_east_ne_zero_of_ne_zero_eq
  {X : Complex}
-- given
  (hX : X ≠ 0) :
-- imply
  isingF 1 X ≠ 0 := by
-- proof
  apply StatMech.Universality.isingF_east_ne_zero_of_ne_zero X hX

/--
[fkIsingSquarePerimeter_configIdentity_not_signReversing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquarePerimeter_configIdentity_not_signReversing_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n)
  (hne : (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterCancelledSide side)) ≠ 0) :
-- imply
  ¬ ∀ rho, (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand ((Equiv.refl _ : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃ _) rho) (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterCancelledSide side)) = -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand rho (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterCancelledSide side)) := by
-- proof
  apply StatMech.Universality.fkIsingSquarePerimeter_configIdentity_not_signReversing n hn side k omega hne

/--
[fkIsingSquarePerimeterCancelled_left_endpoint_mem_wiredArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquarePerimeterCancelled_left_endpoint_mem_wiredArc_eq
  {n : Nat}
  {k : Fin (2 * n)} :
-- imply
  fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n (fkIsingSquarePerimeterEdge n .left k, fkIsingSquarePerimeterCancelledSide .left)) := by
-- proof
  apply StatMech.Universality.fkIsingSquarePerimeterCancelled_left_endpoint_mem_wiredArc n k

/--
[fkIsingSquareWiredPerimeter_cancelled_left_mem_empty_exploration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredPerimeter_cancelled_left_mem_empty_exploration_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (.dart (fkIsingSquarePerimeterEdge n .left k, fkIsingSquarePerimeterCancelledSide .left) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationOrder n hn (FK.edgeSetConfig ∅) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPerimeter_cancelled_left_mem_empty_exploration n hn k

/--
[fkIsingSquareWiredPerimeter_cancelled_left_empty_summand_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredPerimeter_cancelled_left_empty_summand_ne_zero_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand (FK.edgeSetConfig ∅) (.dart (fkIsingSquarePerimeterEdge n .left k, fkIsingSquarePerimeterCancelledSide .left)) ≠ 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPerimeter_cancelled_left_empty_summand_ne_zero n hn k

/--
[fkIsingSquarePerimeter_configIdentity_not_signReversing_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquarePerimeter_configIdentity_not_signReversing_empty_left_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  ¬ ∀ rho, (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand ((Equiv.refl _ : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃ _) rho) (.dart (fkIsingSquarePerimeterEdge n .left k, fkIsingSquarePerimeterCancelledSide .left)) = -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand rho (.dart (fkIsingSquarePerimeterEdge n .left k, fkIsingSquarePerimeterCancelledSide .left)) := by
-- proof
  apply StatMech.Universality.fkIsingSquarePerimeter_configIdentity_not_signReversing_empty_left n hn k

/--
[fkIsingSquarePerimeterEdge_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquarePerimeterEdge_axis_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)} :
-- imply
  (fkIsingSquareOrientedEdge n (fkIsingSquarePerimeterEdge n side k)).axis = match side with := by
-- proof
  apply StatMech.Universality.fkIsingSquarePerimeterEdge_axis n side k

/--
[fkIsingSquarePerimeterRetained_tangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquarePerimeterRetained_tangent_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterRetainedSide side)) = fkIsingSquareBoundaryTangent side := by
-- proof
  apply StatMech.Universality.fkIsingSquarePerimeterRetained_tangent n hn side k

/--
[isingFermionicBoundaryVertexNormSqFactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma isingFermionicBoundaryVertexNormSqFactor_pos_eq :
-- imply
  0 < isingFermionicBoundaryVertexNormSqFactor := by
-- proof
  apply StatMech.Universality.isingFermionicBoundaryVertexNormSqFactor_pos

/--
[isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor_eq :
-- imply
  Real.sqrt 2 / 2 * isingFermionicBoundaryVertexNormSqFactor = isingFermionicGhostCoefficient := by
-- proof
  apply StatMech.Universality.isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor

/--
[fkIsingSquareWiredBoundaryVertexSquareRepresentative_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryVertexSquareRepresentative_normSq_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  Complex.normSq (fkIsingSquareWiredBoundaryVertexSquareRepresentative n hn side k) = isingFermionicBoundaryVertexNormSqFactor * Complex.normSq (fkIsingSquareWiredBoundaryMedialObservable n hn side k) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryVertexSquareRepresentative_normSq n hn side k

/--
[fkIsingSquareWiredBoundaryVertexSquareRepresentative_halfDiagonal_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryVertexSquareRepresentative_halfDiagonal_normSq_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  Real.sqrt 2 / 2 * Complex.normSq (fkIsingSquareWiredBoundaryVertexSquareRepresentative n hn side k) = isingFermionicGhostCoefficient * fkIsingSquareWiredPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterRetainedSide side)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryVertexSquareRepresentative_halfDiagonal_normSq n hn side k

/--
[fkIsingSquareWiredBoundaryMedialObservable_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryMedialObservable_square_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryTangent side * fkIsingSquareWiredBoundaryMedialObservable n hn side k ^ 2 = (fkIsingSquareWiredPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterRetainedSide side)) : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryMedialObservable_square n hn side k

/--
[fkIsingSquareWiredBoundaryVertexSquareRepresentative_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryVertexSquareRepresentative_square_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryTangent side * fkIsingSquareWiredBoundaryVertexSquareRepresentative n hn side k ^ 2 = (isingFermionicBoundaryVertexNormSqFactor * fkIsingSquareWiredPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterRetainedSide side)) : Real) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryVertexSquareRepresentative_square n hn side k

/--
[fkIsingSquareWiredBoundaryMedialObservable_exists_nonnegative_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryMedialObservable_exists_nonnegative_square_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  ∃ t : Real, 0 ≤ t ∧ fkIsingSquareBoundaryTangent side * fkIsingSquareWiredBoundaryMedialObservable n hn side k ^ 2 = (t : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryMedialObservable_exists_nonnegative_square n hn side k

/--
[fkIsingSquareWiredPerimeterInterior_face_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredPerimeterInterior_face_sub_vertex_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) - FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn (fkIsingSquareBoundaryVertex n (side, k)) = fkIsingSquareWiredPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterInteriorSide side)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPerimeterInterior_face_sub_vertex n hn side k

/--
[fkIsingSquareWiredPerimeterInterior_vertex_le_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredPerimeterInterior_vertex_le_face_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn (fkIsingSquareBoundaryVertex n (side, k)) ≤ FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPerimeterInterior_vertex_le_face n hn side k

/--
[fkIsingSquareWiredPerimeterInterior_face_sub_vertex_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredPerimeterInterior_face_sub_vertex_nonneg_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  0 ≤ FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) - FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn (fkIsingSquareBoundaryVertex n (side, k)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPerimeterInterior_face_sub_vertex_nonneg n hn side k

/--
[vertex_modifiedLaplacian_nonpos_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
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
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (vertexPrimitive n hn) x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - vertexPrimitive n hn x) <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.vertex_modifiedLaplacian_nonpos_of_interior n hn x heast hnorth hwest hsouth

/--
[face_modifiedLaplacian_nonneg_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
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
  0 <= isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (facePrimitive n hn) c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - facePrimitive n hn c) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.face_modifiedLaplacian_nonneg_of_interior n hn c heast hnorth hwest hsouth

/--
[fkIsingSquareWiredFullMedialObservable_eq_retained_of_cancellation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredFullMedialObservable_eq_retained_of_cancellation_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
-- imply
  fkIsingSquareWiredFullMedialObservable n hn (fkIsingSquarePerimeterEdge n side k) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterRetainedSide side)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredFullMedialObservable_eq_retained_of_cancellation n hn side k h

/--
[fkIsingSquareWiredFullMedialObservable_boundary_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredFullMedialObservable_boundary_square_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
-- imply
  fkIsingSquareBoundaryTangent side * fkIsingSquareWiredFullMedialObservable n hn (fkIsingSquarePerimeterEdge n side k) ^ 2 = (fkIsingSquareWiredPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquarePerimeterRetainedSide side)) : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredFullMedialObservable_boundary_square n hn side k h

/--
[fkIsingSquareWiredFullMedialObservable_exists_nonnegative_boundary_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredFullMedialObservable_exists_nonnegative_boundary_square_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
-- imply
  ∃ t : Real, 0 ≤ t ∧ fkIsingSquareBoundaryTangent side * fkIsingSquareWiredFullMedialObservable n hn (fkIsingSquarePerimeterEdge n side k) ^ 2 = (t : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredFullMedialObservable_exists_nonnegative_boundary_square n hn side k h

/--
[fkIsingSquareWiredPerimeter_south_increment_eq_north_of_cancellation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredPerimeter_south_increment_eq_north_of_cancellation_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, .south)) = fkIsingSquareWiredPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPerimeter_south_increment_eq_north_of_cancellation n hn side k h

/--
[fkIsingSquarePerimeterMarkedCut_bottom_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquarePerimeterMarkedCut_bottom_first_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquarePerimeterMarkedCut n .bottom (fkIsingSquarePerimeterFirstIndex n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquarePerimeterMarkedCut_bottom_first n hn

/--
[fkIsingSquarePerimeterMarkedCut_top_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquarePerimeterMarkedCut_top_last_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquarePerimeterMarkedCut n .top (fkIsingSquarePerimeterLastIndex n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquarePerimeterMarkedCut_top_last n hn

/--
[fkIsingSquareWiredSourceDart_eq_perimeter_bottom_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredSourceDart_eq_perimeter_bottom_first_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredSourceDart n hn = (fkIsingSquarePerimeterEdge n .bottom (fkIsingSquarePerimeterFirstIndex n hn), .south) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSourceDart_eq_perimeter_bottom_first n hn

/--
[fkIsingSquareWiredTerminalDart_eq_perimeter_top_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWiredTerminalDart_eq_perimeter_top_last_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredTerminalDart n hn = (fkIsingSquarePerimeterEdge n .top (fkIsingSquarePerimeterLastIndex n hn), .west) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredTerminalDart_eq_perimeter_top_last n hn

/--
[fkIsingSquareWired_top_marked_cancelled_observable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean)
-/
@[path]
private lemma fkIsingSquareWired_top_marked_cancelled_observable_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n .top (fkIsingSquarePerimeterLastIndex n hn), fkIsingSquarePerimeterCancelledSide .top)) = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_top_marked_cancelled_observable n hn


-- created on 2026-10-23
