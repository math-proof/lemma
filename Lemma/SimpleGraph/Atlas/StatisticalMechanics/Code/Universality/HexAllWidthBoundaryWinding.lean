import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part4
open StatMech StatMech.Universality


/--
[hsc_genEndpointVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hsc_genEndpointVertices_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 (hsc_negTurns ts)).endpointVertices = (ofTurns a h0 ts).endpointVertices.map (hsc_refl a h0) := by
-- proof
  apply StatMech.Universality.hsc_genEndpointVertices a h0 ts

/--
[hsc_genEndpointIsSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hsc_genEndpointIsSAW_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 ts).EndpointIsSAW) :
-- imply
  (ofTurns a h0 (hsc_negTurns ts)).EndpointIsSAW := by
-- proof
  apply StatMech.Universality.hsc_genEndpointIsSAW a h0 ts hsaw

/--
[hsc_genEndpointIsLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hsc_genEndpointIsLegalSAW_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW) :
-- imply
  (ofTurns a h0 (hsc_negTurns ts)).EndpointIsLegalSAW := by
-- proof
  apply StatMech.Universality.hsc_genEndpointIsLegalSAW a h0 ts hlegal

/--
[hsc_genEndpointNumVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hsc_genEndpointNumVertices_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 (hsc_negTurns ts)).endpointNumVertices = (ofTurns a h0 ts).endpointNumVertices := by
-- proof
  apply StatMech.Universality.hsc_genEndpointNumVertices a h0 ts

/--
[hsc_endpoint_admissible_refl_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hsc_endpoint_admissible_refl_iff_eq
  {a : ℂ}
  {z : ℂ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hsym : ∀ m, region m → region (hsc_refl a h0 m)) :
-- imply
  ((ofTurns a h0 (hsc_negTurns ts)).EndpointIsLegalSAW ∧ (ofTurns a h0 (hsc_negTurns ts)).StaysIn region ∧ (ofTurns a h0 (hsc_negTurns ts)).EndsAt (hsc_refl a h0 z)) ↔ ((ofTurns a h0 ts).EndpointIsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt z) := by
-- proof
  apply StatMech.Universality.hsc_endpoint_admissible_refl_iff region a h0 z hsym ts

/--
[endpointCountWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma endpointCountWeight_nonneg_eq
  {a : ℂ}
  {z : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  0 ≤ endpointCountWeight region a h0 z x ts := by
-- proof
  apply StatMech.Universality.endpointCountWeight_nonneg region a h0 z hx ts

/--
[endpointParafSummand_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma endpointParafSummand_factor_eq
  {a : ℂ}
  {z : ℂ}
  {σ x W : ℝ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hdet : (ofTurns a h0 ts).EndpointIsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt z → (ofTurns a h0 ts).turning = W) :
-- imply
  endpointParafSummand region a h0 z σ x ts = Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ)) * ((endpointCountWeight region a h0 z x ts : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.endpointParafSummand_factor region a h0 z σ x W ts hdet

/--
[endpointParafObservable_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma endpointParafObservable_factor_eq
  {a : ℂ}
  {z : ℂ}
  {σ x W : ℝ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hdet : ∀ ts, (ofTurns a h0 ts).EndpointIsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt z → (ofTurns a h0 ts).turning = W) :
-- imply
  endpointParafObservable region a h0 z σ x = Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ)) * ((endpointCountObservable region a h0 z x : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.endpointParafObservable_factor region a h0 z σ x W hdet

/--
[endpointCountWeight_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma endpointCountWeight_refl_eq
  {a : ℂ}
  {z : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hsym : ∀ m, region m → region (hsc_refl a h0 m)) :
-- imply
  endpointCountWeight region a h0 (hsc_refl a h0 z) x (hsc_negTurns ts) = endpointCountWeight region a h0 z x ts := by
-- proof
  apply StatMech.Universality.endpointCountWeight_refl region a h0 z x hsym ts

/--
[endpointCountObservable_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma endpointCountObservable_refl_eq
  {a : ℂ}
  {z : ℂ}
  {x : ℝ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hsym : ∀ m, region m → region (hsc_refl a h0 m)) :
-- imply
  endpointCountObservable region a h0 (hsc_refl a h0 z) x = endpointCountObservable region a h0 z x := by
-- proof
  apply StatMech.Universality.endpointCountObservable_refl region a h0 z x hsym

/--
[endpoint_det_winding_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma endpoint_det_winding_reflect_eq
  {a : ℂ}
  {z : ℂ}
  {W : ℝ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hsym : ∀ m, region m → region (hsc_refl a h0 m))
  (hdet : ∀ ts, (ofTurns a h0 ts).EndpointIsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt z → (ofTurns a h0 ts).turning = W) :
-- imply
  ∀ ts, (ofTurns a h0 ts).EndpointIsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt (hsc_refl a h0 z) → (ofTurns a h0 ts).turning = -W := by
-- proof
  apply StatMech.Universality.endpoint_det_winding_reflect region a h0 z W hsym hdet

/--
[hexAWNeighborPos_eq_mid_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWNeighborPos_eq_mid_add_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexAWPos (hexAWNeighbor c e) = hexAWMid c e + halfStep (hexAWHeading c e) := by
-- proof
  apply StatMech.Universality.hexAWNeighborPos_eq_mid_add c e

/--
[hexAWEndpoint_finalHeading_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWEndpoint_finalHeading_mod_eq
  {T L : ℕ}
  {e : HexAWIncidence T L}
  {ts : List ℤ}
-- given
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hexit : hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos (hexAWNeighbor e.vtx.1 e.edge)) :
-- imply
  (6 : ℤ) ∣ (hexInfra_headAccum 1 ts - hexAWHeading e.vtx.1 e.edge) := by
-- proof
  apply StatMech.Universality.hexAWEndpoint_finalHeading_mod e ts hend hexit

/--
[hexAWEndpoint_finalHeading_eq_of_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWEndpoint_finalHeading_eq_of_window_eq
  {T L : ℕ}
  {e : HexAWIncidence T L}
  {ts : List ℤ}
  {w : ℤ}
-- given
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hexit : hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos (hexAWNeighbor e.vtx.1 e.edge))
  (hwalkL : w ≤ hexInfra_headAccum 1 ts)
  (hwalkU : hexInfra_headAccum 1 ts < w + 6)
  (hedgeL : w ≤ hexAWHeading e.vtx.1 e.edge)
  (hedgeU : hexAWHeading e.vtx.1 e.edge < w + 6) :
-- imply
  hexInfra_headAccum 1 ts = hexAWHeading e.vtx.1 e.edge := by
-- proof
  apply StatMech.Universality.hexAWEndpoint_finalHeading_eq_of_window e ts w hend hexit hwalkL hwalkU hedgeL hedgeU

/--
[hexAWEndpoint_turning_eq_of_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWEndpoint_turning_eq_of_window_eq
  {T L : ℕ}
  {e : HexAWIncidence T L}
  {ts : List ℤ}
  {w : ℤ}
-- given
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hexit : hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos (hexAWNeighbor e.vtx.1 e.edge))
  (hwalkL : w ≤ hexInfra_headAccum 1 ts)
  (hwalkU : hexInfra_headAccum 1 ts < w + 6)
  (hedgeL : w ≤ hexAWHeading e.vtx.1 e.edge)
  (hedgeU : hexAWHeading e.vtx.1 e.edge < w + 6) :
-- imply
  (ofTurns hexAWStart 1 ts).turning = (Real.pi / 3) * ((hexAWHeading e.vtx.1 e.edge : ℝ) - 1) := by
-- proof
  apply StatMech.Universality.hexAWEndpoint_turning_eq_of_window e ts w hend hexit hwalkL hwalkU hedgeL hedgeU

/--
[hexAWLowerSlantWitnessCoord_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWLowerSlantWitnessCoord_mem_eq
  {L : ℕ} :
-- imply
  hexAWLowerSlantWitnessCoord L ∈ hexAWVertexSet 2 L := by
-- proof
  apply StatMech.Universality.hexAWLowerSlantWitnessCoord_mem L

/--
[hexAWUpperSlantWitnessCoord_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWUpperSlantWitnessCoord_mem_eq
  {L : ℕ} :
-- imply
  hexAWUpperSlantWitnessCoord L ∈ hexAWVertexSet 2 L := by
-- proof
  apply StatMech.Universality.hexAWUpperSlantWitnessCoord_mem L

/--
[hexAWLowerSlantWitness_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWLowerSlantWitness_heading_eq
  {L : ℕ} :
-- imply
  hexAWHeading (hexAWLowerSlantWitness L).vtx.1 (hexAWLowerSlantWitness L).edge = 0 := by
-- proof
  apply StatMech.Universality.hexAWLowerSlantWitness_heading L

/--
[hexAWUpperSlantWitness_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWUpperSlantWitness_heading_eq
  {L : ℕ} :
-- imply
  hexAWHeading (hexAWUpperSlantWitness L).vtx.1 (hexAWUpperSlantWitness L).edge = 2 := by
-- proof
  apply StatMech.Universality.hexAWUpperSlantWitness_heading L

/--
[hexAWLowerSlantWitness_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWLowerSlantWitness_mem_boundary_eq
  {L : ℕ} :
-- imply
  hexAWLowerSlantWitness L ∈ hexAWBoundaryIncidences 2 L := by
-- proof
  apply StatMech.Universality.hexAWLowerSlantWitness_mem_boundary L

/--
[hexAWUpperSlantWitness_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWUpperSlantWitness_mem_boundary_eq
  {L : ℕ} :
-- imply
  hexAWUpperSlantWitness L ∈ hexAWBoundaryIncidences 2 L := by
-- proof
  apply StatMech.Universality.hexAWUpperSlantWitness_mem_boundary L

/--
[hexAWLowerSlant_turning_ne_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWLowerSlant_turning_ne_source_eq
  {L : ℕ}
  {ts : List ℤ}
-- given
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid (hexAWLowerSlantWitness L).vtx.1 (hexAWLowerSlantWitness L).edge))
  (hexit : hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos (hexAWNeighbor (hexAWLowerSlantWitness L).vtx.1 (hexAWLowerSlantWitness L).edge)) :
-- imply
  (ofTurns hexAWStart 1 ts).turning ≠ -(2 * Real.pi / 3) := by
-- proof
  apply StatMech.Universality.hexAWLowerSlant_turning_ne_source L ts hend hexit

/--
[hexAWUpperSlant_turning_ne_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean)
-/
@[path]
private lemma hexAWUpperSlant_turning_ne_source_eq
  {L : ℕ}
  {ts : List ℤ}
-- given
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid (hexAWUpperSlantWitness L).vtx.1 (hexAWUpperSlantWitness L).edge))
  (hexit : hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos (hexAWNeighbor (hexAWUpperSlantWitness L).vtx.1 (hexAWUpperSlantWitness L).edge)) :
-- imply
  (ofTurns hexAWStart 1 ts).turning ≠ 2 * Real.pi / 3 := by
-- proof
  apply StatMech.Universality.hexAWUpperSlant_turning_ne_source L ts hend hexit


-- created on 2026-10-23
