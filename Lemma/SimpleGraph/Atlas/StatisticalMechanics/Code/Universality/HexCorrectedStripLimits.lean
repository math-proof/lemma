import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
open StatMech StatMech.Universality


/--
[hexCSInStrip_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSInStrip_mono_eq
  {T T' L L' : ℕ}
  {c : HexAWCoord}
-- given
  (hT : T ≤ T')
  (hL : L ≤ L')
  (hc : hexCSInStrip T L c) :
-- imply
  hexCSInStrip T' L' c := by
-- proof
  apply StatMech.Universality.hexCSInStrip_mono hT hL c hc

/--
[hexCSVertexSet_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSVertexSet_mono_eq
  {T T' L L' : ℕ}
-- given
  (hT : T ≤ T')
  (hL : L ≤ L') :
-- imply
  hexCSVertexSet T L ⊆ hexCSVertexSet T' L' := by
-- proof
  apply StatMech.Universality.hexCSVertexSet_mono hT hL

/--
[hexCSMids_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSMids_mono_eq
  {T T' L L' : ℕ}
-- given
  (hT : T ≤ T')
  (hL : L ≤ L') :
-- imply
  hexCSMids T L ⊆ hexCSMids T' L' := by
-- proof
  apply StatMech.Universality.hexCSMids_mono hT hL

/--
[hexCSFiniteRegion_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSFiniteRegion_mono_eq
  {T T' L L' : ℕ}
  {hpos : 0 < T}
  {hpos' : 0 < T'}
  {z : ℂ}
-- given
  (hT : T ≤ T')
  (hL : L ≤ L')
  (hz : (hexCSFiniteRegion T L hpos).inRegion z) :
-- imply
  (hexCSFiniteRegion T' L' hpos').inRegion z := by
-- proof
  apply StatMech.Universality.hexCSFiniteRegion_mono hT hL z hz

/--
[hexCSFiniteRegion_mono_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSFiniteRegion_mono_L_eq
  {T L L' : ℕ}
  {hpos : 0 < T}
  {z : ℂ}
-- given
  (hL : L ≤ L') :
-- imply
  (hexCSFiniteRegion T L hpos).inRegion z → (hexCSFiniteRegion T L' hpos).inRegion z := by
-- proof
  apply StatMech.Universality.hexCSFiniteRegion_mono_L hL z

/--
[hexCSFiniteRegion_mono_T](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSFiniteRegion_mono_T_eq
  {T T' L : ℕ}
  {hpos : 0 < T}
  {hpos' : 0 < T'}
  {z : ℂ}
-- given
  (hT : T ≤ T') :
-- imply
  (hexCSFiniteRegion T L hpos).inRegion z → (hexCSFiniteRegion T' L hpos').inRegion z := by
-- proof
  apply StatMech.Universality.hexCSFiniteRegion_mono_T hT z

/--
[endpointStaysIn_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma endpointStaysIn_mono_eq
  {region region' : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {ts : List ℤ}
-- given
  (hsub : ∀ z, region z → region' z)
  (hstay : (ofTurns a h0 ts).StaysIn region) :
-- imply
  (ofTurns a h0 ts).StaysIn region' := by
-- proof
  apply StatMech.Universality.endpointStaysIn_mono hsub hstay

/--
[endpointCountWeight_mono_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma endpointCountWeight_mono_region_eq
  {region region' : ℂ → Prop}
  {a : ℂ}
  {z : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hsub : ∀ m, region m → region' m) :
-- imply
  endpointCountWeight region a h0 z x ts ≤ endpointCountWeight region' a h0 z x ts := by
-- proof
  apply StatMech.Universality.endpointCountWeight_mono_region a h0 z hx hsub ts

/--
[HexFiniteRegion.endpointCountWeight_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma endpointCountWeight_summable_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {z : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  Summable (fun ts : List ℤ => endpointCountWeight R.inRegion a h0 z x ts) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointCountWeight_summable R a h0 z x

/--
[endpointCountObservable_mono_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma endpointCountObservable_mono_finite_eq
  {R R' : HexFiniteRegion}
  {a : ℂ}
  {z : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hsub : ∀ m, R.inRegion m → R'.inRegion m) :
-- imply
  endpointCountObservable R.inRegion a h0 z x ≤ endpointCountObservable R'.inRegion a h0 z x := by
-- proof
  apply StatMech.Universality.endpointCountObservable_mono_finite R R' a h0 z hx hsub

/--
[hexCS_endpointCountObservable_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCS_endpointCountObservable_mono_eq
  {T T' L L' : ℕ}
  {hpos : 0 < T}
  {hpos' : 0 < T'}
  {z : ℂ}
-- given
  (hT : T ≤ T')
  (hL : L ≤ L') :
-- imply
  endpointCountObservable (hexCSFiniteRegion T L hpos).inRegion hexAWStart 1 z hexChi ≤ endpointCountObservable (hexCSFiniteRegion T' L' hpos').inRegion hexAWStart 1 z hexChi := by
-- proof
  apply StatMech.Universality.hexCS_endpointCountObservable_mono hT hL z

/--
[hexCSSideWalk_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSSideWalk_mono_eq
  {T T' L L' : ℕ}
  {hpos : 0 < T}
  {hpos' : 0 < T'}
  {ts : List ℤ}
-- given
  (hT : T ≤ T')
  (hL : L ≤ L')
  (hwalk : HexCSSideWalk T L hpos ts) :
-- imply
  HexCSSideWalk T' L' hpos' ts := by
-- proof
  apply StatMech.Universality.hexCSSideWalk_mono hT hL hwalk

/--
[hexCSTopWalk_mono_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSTopWalk_mono_L_eq
  {T L L' : ℕ}
  {hpos : 0 < T}
  {ts : List ℤ}
-- given
  (hL : L ≤ L')
  (hwalk : HexCSTopWalk T L hpos ts) :
-- imply
  HexCSTopWalk T L' hpos ts := by
-- proof
  apply StatMech.Universality.hexCSTopWalk_mono_L hL hwalk

/--
[hexCSTopWalk_subset_atWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSTopWalk_subset_atWidth_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  ∀ ts, HexCSTopWalk T L hT ts → HexCSTopWalkAtWidth T hT ts := by
-- proof
  apply StatMech.Universality.hexCSTopWalk_subset_atWidth T L hT

/--
[hexCSTopWalkHeight_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSTopWalkHeight_spec_eq
  {T : ℕ}
  {hT : 0 < T}
  {w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}} :
-- imply
  HexCSTopWalk T (hexCSTopWalkHeight w) hT w.1 := by
-- proof
  apply StatMech.Universality.hexCSTopWalkHeight_spec w

/--
[hexCSTopWalk_finset_fits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSTopWalk_finset_fits_eq
  {T : ℕ}
  {hT : 0 < T}
  {s : Finset {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}}
  {w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}}
-- given
  (hw : w ∈ s) :
-- imply
  HexCSTopWalk T (hexCSTopFinsetHeight s) hT w.1 := by
-- proof
  apply StatMech.Universality.hexCSTopWalk_finset_fits s w hw

/--
[hexAWNeighbor_color_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexAWNeighbor_color_ne_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  (hexAWNeighbor c e).color ≠ c.color := by
-- proof
  apply StatMech.Universality.hexAWNeighbor_color_ne c e

/--
[hexAWMid_white_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexAWMid_white_injective_eq
  {c d : HexAWCoord}
  {e f : Fin 3}
-- given
  (hc : c.color = .white)
  (hd : d.color = .white)
  (hm : hexAWMid c e = hexAWMid d f) :
-- imply
  c = d ∧ e = f := by
-- proof
  apply StatMech.Universality.hexAWMid_white_injective hc hd hm

/--
[hexCSSlantWalk_height_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSSlantWalk_height_unique_eq
  {T L L' : ℕ}
  {hT : 0 < T}
  {ts : List ℤ}
-- given
  (hL : HexCSSlantWalk T L hT ts)
  (hL' : HexCSSlantWalk T L' hT ts) :
-- imply
  L = L' := by
-- proof
  apply StatMech.Universality.hexCSSlantWalk_height_unique hL hL'

/--
[hexCSSlantWalkHeight_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSSlantWalkHeight_spec_eq
  {T : ℕ}
  {hT : 0 < T}
  {w : {ts : List ℤ // HexCSSlantWalkAtWidth T hT ts}} :
-- imply
  HexCSSlantWalk T (hexCSSlantWalkHeight w) hT w.1 := by
-- proof
  apply StatMech.Universality.hexCSSlantWalkHeight_spec w

/--
[hexCSSlantWalkHeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean)
-/
@[path]
private lemma hexCSSlantWalkHeight_eq_eq
  {T L : ℕ}
  {hT : 0 < T}
  {w : {ts : List ℤ // HexCSSlantWalkAtWidth T hT ts}}
-- given
  (hw : HexCSSlantWalk T L hT w.1) :
-- imply
  hexCSSlantWalkHeight w = L := by
-- proof
  apply StatMech.Universality.hexCSSlantWalkHeight_eq w hw


-- created on 2026-10-23
