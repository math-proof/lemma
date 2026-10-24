import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer
open StatMech StatMech.Universality


/--
[fkIsingSquareClosePerimeter_perimeterEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareClosePerimeter_perimeterEdge_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)} :
-- imply
  fkIsingSquareClosePerimeter n omega (fkIsingSquarePerimeterEdge n side k).1 = false := by
-- proof
  apply StatMech.Universality.fkIsingSquareClosePerimeter_perimeterEdge n omega side k

/--
[setClosed_fkIsingSquareClosePerimeter_perimeterEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma setClosed_fkIsingSquareClosePerimeter_perimeterEdge_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)} :
-- imply
  setClosed (fkIsingSquarePerimeterEdge n side k).1 (fkIsingSquareClosePerimeter n omega) = fkIsingSquareClosePerimeter n omega := by
-- proof
  apply StatMech.Universality.setClosed_fkIsingSquareClosePerimeter_perimeterEdge n omega side k

/--
[fkIsingSquareBoundaryLayerInwardSide_eq_interiorSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerInwardSide_eq_interiorSide_eq
  {side : FKIsingSquareBoundarySide} :
-- imply
  fkIsingSquareBoundaryLayerInwardSide side = fkIsingSquarePerimeterInteriorSide side := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerInwardSide_eq_interiorSide side

/--
[fkIsingSquareBoundaryLayer_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_localMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)} :
-- imply
  FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega) (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side) = (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerEndpointSide side) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_localMate n omega side k

/--
[fkIsingSquareBoundaryLayer_complement_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_complement_localMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)} :
-- imply
  FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega) (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side) = (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementEndpointSide side) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_complement_localMate n omega side k

/--
[fkIsingSquareBoundaryLayer_mem_inward_iff_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_mem_inward_iff_endpoint_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side) : FKIsingSquareWiredCarrier n) ∈ (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega <-> (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerEndpointSide side) : FKIsingSquareWiredCarrier n) ∈ (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_mem_inward_iff_endpoint n hn omega side k

/--
[fkIsingSquareBoundaryLayer_winding_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_winding_endpoint_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hmem : (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side) : FKIsingSquareWiredCarrier n) ∈ (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerEndpointSide side)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side)) - Real.pi / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_winding_endpoint n hn omega side k hmem

/--
[fkIsingSquareBoundaryLayer_windingPhase_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_windingPhase_endpoint_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hmem : (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side) : FKIsingSquareWiredCarrier n) ∈ (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerEndpointSide side)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda⁻¹ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_windingPhase_endpoint n hn omega side k hmem

/--
[fkIsingSquareBoundaryLayer_fermionicSummand_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_fermionicSummand_endpoint_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerEndpointSide side)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda⁻¹ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_fermionicSummand_endpoint n hn omega side k

/--
[fkIsingSquareBoundaryLayer_fermionicObservable_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_fermionicObservable_endpoint_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerEndpointSide side)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda⁻¹ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_fermionicObservable_endpoint n hn side k

/--
[fkIsingSquareBoundaryLayer_mem_complement_inward_iff_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_mem_complement_inward_iff_endpoint_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side) : FKIsingSquareWiredCarrier n) ∈ (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega <-> (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementEndpointSide side) : FKIsingSquareWiredCarrier n) ∈ (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_mem_complement_inward_iff_endpoint n hn omega side k

/--
[fkIsingSquareBoundaryLayer_winding_complement_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_winding_complement_endpoint_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hmem : (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side) : FKIsingSquareWiredCarrier n) ∈ (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementEndpointSide side)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side)) - Real.pi / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_winding_complement_endpoint n hn omega side k hmem

/--
[fkIsingSquareBoundaryLayer_windingPhase_complement_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_windingPhase_complement_endpoint_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hmem : (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side) : FKIsingSquareWiredCarrier n) ∈ (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementEndpointSide side)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side)) * isingLambda⁻¹ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_windingPhase_complement_endpoint n hn omega side k hmem

/--
[fkIsingSquareBoundaryLayer_fermionicSummand_complement_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_fermionicSummand_complement_endpoint_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementEndpointSide side)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand omega (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side)) * isingLambda⁻¹ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_fermionicSummand_complement_endpoint n hn omega side k

/--
[fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementEndpointSide side)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side)) * isingLambda⁻¹ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint n hn side k

/--
[isingFermionicBoundaryVertexNormalization_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma isingFermionicBoundaryVertexNormalization_pos_eq :
-- imply
  0 < isingFermionicBoundaryVertexNormalization := by
-- proof
  apply StatMech.Universality.isingFermionicBoundaryVertexNormalization_pos

/--
[fkIsingSquareBoundaryLayerInward_directedTangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerInward_directedTangent_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side)) = match side with := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerInward_directedTangent n hn side k

/--
[fkIsingSquareBoundaryLayerNormal_mul_edgeSumFactor_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerNormal_mul_edgeSumFactor_sq_eq
  {side : FKIsingSquareBoundarySide} :
-- imply
  fkIsingSquareBoundaryLayerNormal side * (1 + isingLambda⁻¹) ^ 2 = ((2 + Real.sqrt 2 : Real) : Complex) * match side with := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerNormal_mul_edgeSumFactor_sq side

/--
[fkIsingSquareBoundaryLayer_windingPhase_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_windingPhase_sq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hz : z ∈ (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega z ^ 2 = fkIsingSquareWiredDirectedPhase n hn z ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_windingPhase_sq n hn omega z hz

/--
[fkIsingSquareBoundaryLayer_inward_exists_nonnegative_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_inward_exists_nonnegative_square_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  ∃ t : Real, 0 <= t ∧ fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side)) * ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side))) ^ 2 = (t : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_inward_exists_nonnegative_square n hn side k

/--
[fkIsingSquareBoundaryLayerVertexFermion_exists_nonnegative_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerVertexFermion_exists_nonnegative_square_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  ∃ t : Real, 0 <= t ∧ fkIsingSquareBoundaryLayerNormal side * fkIsingSquareBoundaryLayerVertexFermion n hn side k ^ 2 = (t : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerVertexFermion_exists_nonnegative_square n hn side k

/--
[isingFermionicBoundaryVertexNormalization_sq_mul_edgeSumNormSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma isingFermionicBoundaryVertexNormalization_sq_mul_edgeSumNormSq_eq :
-- imply
  isingFermionicBoundaryVertexNormalization ^ 2 * (2 + Real.sqrt 2) = isingFermionicBoundaryVertexNormSqFactor := by
-- proof
  apply StatMech.Universality.isingFermionicBoundaryVertexNormalization_sq_mul_edgeSumNormSq

/--
[isingLambda_inv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma isingLambda_inv_val_eq :
-- imply
  isingLambda⁻¹ = (1 - Complex.I) / (Real.sqrt 2 : Complex) := by
-- proof
  apply StatMech.Universality.isingLambda_inv_val

/--
[isingLambda_one_add_inv_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma isingLambda_one_add_inv_normSq_eq :
-- imply
  Complex.normSq (1 + isingLambda⁻¹) = 2 + Real.sqrt 2 := by
-- proof
  apply StatMech.Universality.isingLambda_one_add_inv_normSq

/--
[fkIsingSquareBoundaryLayerVertexFermion_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerVertexFermion_normSq_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  Complex.normSq (fkIsingSquareBoundaryLayerVertexFermion n hn side k) = isingFermionicBoundaryVertexNormSqFactor * Complex.normSq ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerVertexFermion_normSq n hn side k

/--
[fkIsingSquareBoundaryLayerInwardIncrement_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerInwardIncrement_nonneg_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  0 <= fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerInwardIncrement_nonneg n hn side k

/--
[fkIsingSquareBoundaryLayerFirstFaceTrace_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerFirstFaceTrace_sub_vertex_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryLayerFirstFaceTrace n hn side k - FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn (fkIsingSquareBoundaryVertex n (side, k)) = fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerFirstFaceTrace_sub_vertex n hn side k

/--
[fkIsingSquareBoundaryLayer_vertex_le_firstFaceTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_vertex_le_firstFaceTrace_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn (fkIsingSquareBoundaryVertex n (side, k)) <= fkIsingSquareBoundaryLayerFirstFaceTrace n hn side k := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_vertex_le_firstFaceTrace n hn side k

/--
[fkIsingSquareBoundaryLayer_halfDiagonal_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_halfDiagonal_normSq_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  Real.sqrt 2 / 2 * Complex.normSq (fkIsingSquareBoundaryLayerVertexFermion n hn side k) = isingFermionicGhostCoefficient * fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_halfDiagonal_normSq n hn side k

/--
[fkIsingSquareBoundaryLayer_fermionicSummand_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_fermionicSummand_incidence_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand omega (.bond d) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand omega (.dart d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_fermionicSummand_incidence n hn omega d

/--
[fkIsingSquareBoundaryLayer_fermionicObservable_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_fermionicObservable_incidence_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.bond d) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_fermionicObservable_incidence n hn d

/--
[fkIsingSquareBoundaryLayer_fermionicSummand_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_fermionicSummand_bondMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand omega (.bond (fkIsingSquareWiredBondMate n hn d)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand omega (.bond d) * fkIsingSquareWiredBondPhase n hn d := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_fermionicSummand_bondMate n hn omega d hsource hterminal

/--
[fkIsingSquareBoundaryLayer_fermionicObservable_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_fermionicObservable_bondMate_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.bond (fkIsingSquareWiredBondMate n hn d)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.bond d) * fkIsingSquareWiredBondPhase n hn d := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_fermionicObservable_bondMate n hn d hsource hterminal

/--
[fkIsingSquareBoundaryLayerRadialIncrement_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerRadialIncrement_mk_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryLayerRadialIncrement n hn (Quot.mk _ d) = Complex.normSq ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart d.1)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerRadialIncrement_mk n hn d

/--
[fkIsingSquareBoundaryLayerRadialIncrement_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerRadialIncrement_nonneg_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  0 <= fkIsingSquareBoundaryLayerRadialIncrement n hn e := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerRadialIncrement_nonneg n hn e


-- created on 2026-10-23
