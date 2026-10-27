import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
open StatMech StatMech.Universality StatMech.Universality.HexFiniteRegion StatMech.Universality.HexFObsBoundaryData StatMech.Universality.HexFiniteStripBoundaryData


/--
[hexLegalSAW_eq_nil_of_lastVertex_eq_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexLegalSAW_eq_nil_of_lastVertex_eq_first_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 ts).IsLegalSAW)
  (hlast : hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) = a + halfStep h0) :
-- imply
  ts = [] := by
-- proof
  apply StatMech.Universality.hexLegalSAW_eq_nil_of_lastVertex_eq_first a h0 ts hsaw hlast

/--
[not_startInteriorUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma not_startInteriorUnique_eq
  {R : HexFiniteRegion}
-- given
  (h0 : ℤ) :
-- imply
  ¬R.StartInteriorUnique h0 := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.not_startInteriorUnique R h0

/--
[hexStrip_finiteRegion_not_startInteriorUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexStrip_finiteRegion_not_startInteriorUnique_eq
  {M : Finset ℂ}
  {a : ℂ}
-- given
  (ha : a ∈ M)
  (h0 : ℤ) :
-- imply
  ¬(hexStrip_finiteRegion M a ha).StartInteriorUnique h0 := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hexStrip_finiteRegion_not_startInteriorUnique M a ha h0

/--
[hexStripDirMids_final_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexStripDirMids_final_mem_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (hexInfra_midAccum m h ts, hexInfra_headAccum h ts) ∈ hexStripDirMids m h ts := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hexStripDirMids_final_mem m h ts

/--
[hexStart_midsAux_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexStart_midsAux_prefix_eq
  {m : ℂ}
  {s ts : List ℤ}
-- given
  (h : ℤ)
  (hst : s <+: ts) :
-- imply
  midsAux m h s <+: midsAux m h ts := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hexStart_midsAux_prefix m h hst

/--
[hexStart_verticesAux_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexStart_verticesAux_prefix_eq
  {m : ℂ}
  {s ts : List ℤ}
-- given
  (h : ℤ)
  (hst : s <+: ts) :
-- imply
  verticesAux m h s <+: verticesAux m h ts := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hexStart_verticesAux_prefix m h hst

/--
[hexStart_isLegalSAW_of_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexStart_isLegalSAW_of_prefix_eq
  {a : ℂ}
  {s ts : List ℤ}
-- given
  (h0 : ℤ)
  (hst : s <+: ts)
  (hlegal : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (ofTurns a h0 s).IsLegalSAW := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hexStart_isLegalSAW_of_prefix a h0 hst hlegal

/--
[hexStart_staysIn_of_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexStart_staysIn_of_prefix_eq
  {a : ℂ}
  {s ts : List ℤ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hst : s <+: ts)
  (hstay : (ofTurns a h0 ts).StaysIn inRegion) :
-- imply
  (ofTurns a h0 s).StaysIn inRegion := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hexStart_staysIn_of_prefix inRegion a h0 hst hstay

/--
[hexStripDirMids_mem_prefix_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexStripDirMids_mem_prefix_state_eq
  {m : ℂ}
  {ts : List ℤ}
  {p : ℂ × ℤ}
-- given
  (h : ℤ)
  (hp : p ∈ hexStripDirMids m h ts) :
-- imply
  ∃ s : List ℤ, s <+: ts ∧ p = (hexInfra_midAccum m h s, hexInfra_headAccum h s) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hexStripDirMids_mem_prefix_state m h ts p hp

/--
[returningSAW_eq_nil_of_straightStart_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma returningSAW_eq_nil_of_straightStart_reverse_eq
  {R : HexFiniteRegion}
  {S : HexStraightSide R.inRegion interior R.start h0 R.start}
-- given
  (h0 : ℤ)
  (interior : ℂ → Prop)
  (hreverse : halfStep S.H = -halfStep h0) :
-- imply
  ∀ ts : List ℤ, (ofTurns R.start h0 ts).IsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.returningSAW_eq_nil_of_straightStart_reverse R h0 interior S hreverse

/--
[returningSAW_eq_nil_of_directedStartIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma returningSAW_eq_nil_of_directedStartIncidence_eq
  {R : HexFiniteRegion}
  {S : R.DirectedStartIncidence h0}
-- given
  (h0 : ℤ) :
-- imply
  ∀ ts : List ℤ, (ofTurns R.start h0 ts).IsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.returningSAW_eq_nil_of_directedStartIncidence R h0 S

/--
[hexStrip_singleRegion_legal_stays_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexStrip_singleRegion_legal_stays_eq_nil_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).IsLegalSAW)
  (hstay : (ofTurns a h0 ts).StaysIn (hexStrip_singleRegion a).inRegion) :
-- imply
  ts = [] := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hexStrip_singleRegion_legal_stays_eq_nil a h0 ts hlegal hstay

/--
[hexStrip_singleRegion_returningSAW_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexStrip_singleRegion_returningSAW_eq_nil_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  ∀ ts : List ℤ, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn (hexStrip_singleRegion a).inRegion ∧ (ofTurns a h0 ts).EndsAt a → ts = [] := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hexStrip_singleRegion_returningSAW_eq_nil a h0

/--
[hexStrip_singleRegion_directedStartIncidence_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma hexStrip_singleRegion_directedStartIncidence_nonempty_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Nonempty ((hexStrip_singleRegion a).DirectedStartIncidence h0) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.hexStrip_singleRegion_directedStartIncidence_nonempty a h0

/--
[returningSAW_eq_nil_of_startInteriorUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma returningSAW_eq_nil_of_startInteriorUnique_eq
  {R : HexFiniteRegion}
-- given
  (h0 : ℤ)
  (hstart : R.StartInteriorUnique h0) :
-- imply
  ∀ ts : List ℤ, (ofTurns R.start h0 ts).IsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.returningSAW_eq_nil_of_startInteriorUnique R h0 hstart

/--
[returningSAW_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma returningSAW_eq_nil_eq
  {R : HexFiniteRegion}
-- given
  (h0 : ℤ) :
-- imply
  ∀ ts : List ℤ, (ofTurns R.start h0 ts).IsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.returningSAW_eq_nil R h0

/--
[parafObservable_start_eq_weight_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma parafObservable_start_eq_weight_of_unique_eq
  {a : ℂ}
  {sigma x : ℝ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hreg : inRegion a)
  (hunique : ∀ ts : List ℤ, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion ∧ (ofTurns a h0 ts).EndsAt a → ts = []) :
-- imply
  parafObservable inRegion a h0 a sigma x = (x : ℂ) := by
-- proof
  apply StatMech.Universality.parafObservable_start_eq_weight_of_unique inRegion a h0 sigma x hreg hunique

/--
[parafObservable_start_eq_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma parafObservable_start_eq_weight_eq
  {a : ℂ}
  {sigma x : ℝ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hreg : inRegion a) :
-- imply
  parafObservable inRegion a h0 a sigma x = (x : ℂ) := by
-- proof
  apply StatMech.Universality.parafObservable_start_eq_weight inRegion a h0 sigma x hreg

/--
[boundaryIdentity_fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma boundaryIdentity_fa_eq
  {B : HexFObsBoundaryData} :
-- imply
  hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = B.Fa := by
-- proof
  apply StatMech.Universality.HexFObsBoundaryData.boundaryIdentity_fa B

/--
[boundary_identity_fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma boundary_identity_fa_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = B.Fa := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.boundary_identity_fa

/--
[normalized_boundary_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma normalized_boundary_identity_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
-- given
  (hFa : B.Fa = hexChi) :
-- imply
  hexBdryCl * (hexChi⁻¹ * B.lam) + hexBdryCt * (hexChi⁻¹ * B.tau) + hexChi⁻¹ * B.ups = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.normalized_boundary_identity hFa

/--
[normalized_contour_boundary_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma normalized_contour_boundary_identity_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
-- given
  (hFa : B.Fa = hexChi) :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi)) + hexChi⁻¹ * hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.normalized_contour_boundary_identity hFa

/--
[Fa_eq_hexChi_of_unique_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma Fa_eq_hexChi_of_unique_start_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
-- given
  (hreg : R.inRegion R.start)
  (hunique : ∀ ts : List ℤ, (ofTurns R.start h0 ts).IsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = []) :
-- imply
  B.Fa = hexChi := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.Fa_eq_hexChi_of_unique_start hreg hunique

/--
[Fa_eq_hexChi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma Fa_eq_hexChi_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  B.Fa = hexChi := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.Fa_eq_hexChi

/--
[normalized_boundary_identity_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma normalized_boundary_identity_closed_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  hexBdryCl * (hexChi⁻¹ * B.lam) + hexBdryCt * (hexChi⁻¹ * B.tau) + hexChi⁻¹ * B.ups = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.normalized_boundary_identity_closed

/--
[normalized_contour_boundary_identity_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma normalized_contour_boundary_identity_closed_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V} :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi)) + hexChi⁻¹ * hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.normalized_contour_boundary_identity_closed

/--
[normalized_contour_boundary_identity_of_unique_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma normalized_contour_boundary_identity_of_unique_start_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
-- given
  (hreg : R.inRegion R.start)
  (hunique : ∀ ts : List ℤ, (ofTurns R.start h0 ts).IsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = []) :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi)) + hexChi⁻¹ * hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.normalized_contour_boundary_identity_of_unique_start hreg hunique

/--
[Fa_eq_hexChi_of_directedStartIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma Fa_eq_hexChi_of_directedStartIncidence_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {S : R.DirectedStartIncidence h0} :
-- imply
  B.Fa = hexChi := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.Fa_eq_hexChi_of_directedStartIncidence S

/--
[normalized_contour_boundary_identity_of_directedStartIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma normalized_contour_boundary_identity_of_directedStartIncidence_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {S : R.DirectedStartIncidence h0} :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi)) + hexChi⁻¹ * hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.normalized_contour_boundary_identity_of_directedStartIncidence S

/--
[Fa_eq_hexChi_of_straightStart_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma Fa_eq_hexChi_of_straightStart_reverse_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {S : HexStraightSide R.inRegion interior R.start h0 R.start}
-- given
  (interior : ℂ → Prop)
  (hreverse : halfStep S.H = -halfStep h0) :
-- imply
  B.Fa = hexChi := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.Fa_eq_hexChi_of_straightStart_reverse interior S hreverse

/--
[normalized_contour_boundary_identity_of_straightStart_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma normalized_contour_boundary_identity_of_straightStart_reverse_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {S : HexStraightSide R.inRegion interior R.start h0 R.start}
-- given
  (interior : ℂ → Prop)
  (hreverse : halfStep S.H = -halfStep h0) :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi)) + hexChi⁻¹ * hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.normalized_contour_boundary_identity_of_straightStart_reverse interior S hreverse

/--
[Fa_eq_hexChi_of_stripStartGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma Fa_eq_hexChi_of_stripStartGeometry_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
-- given
  (dregion : ℂ → ℤ → Prop)
  (huniq : ∀ h : ℤ, hexStripInterior dregion (R.start + halfStep h) → halfStep h = halfStep h0)
  (hbridge : ∀ ts : List ℤ, (ofTurns R.start h0 ts).IsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt R.start → hexStripStaysInDir dregion R.start h0 ts) :
-- imply
  B.Fa = hexChi := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.Fa_eq_hexChi_of_stripStartGeometry dregion huniq hbridge

/--
[normalized_contour_boundary_identity_of_stripStartGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma normalized_contour_boundary_identity_of_stripStartGeometry_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
-- given
  (dregion : ℂ → ℤ → Prop)
  (huniq : ∀ h : ℤ, hexStripInterior dregion (R.start + halfStep h) → halfStep h = halfStep h0)
  (hbridge : ∀ ts : List ℤ, (ofTurns R.start h0 ts).IsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt R.start → hexStripStaysInDir dregion R.start h0 ts) :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi)) + hexChi⁻¹ * hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.normalized_contour_boundary_identity_of_stripStartGeometry dregion huniq hbridge

/--
[Fa_eq_hexChi_singleRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma Fa_eq_hexChi_singleRegion_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {a : ℂ}
  {B₁ : HexFiniteStripBoundaryData (hexStrip_singleRegion a) h0 D P} :
-- imply
  B₁.Fa = hexChi := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.Fa_eq_hexChi_singleRegion B₁

/--
[normalized_contour_boundary_identity_singleRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma normalized_contour_boundary_identity_singleRegion_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {a : ℂ}
  {B₁ : HexFiniteStripBoundaryData (hexStrip_singleRegion a) h0 D P} :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda (hexStrip_singleRegion a).inRegion a h0 B₁.sides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus (hexStrip_singleRegion a).inRegion a h0 B₁.sides hexChi + hexContourTauMinus (hexStrip_singleRegion a).inRegion a h0 B₁.sides hexChi)) + hexChi⁻¹ * hexContourUpsilon (hexStrip_singleRegion a).inRegion a h0 B₁.sides hexChi = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.normalized_contour_boundary_identity_singleRegion B₁

/--
[Fa_eq_hexChi_of_startInteriorUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma Fa_eq_hexChi_of_startInteriorUnique_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
-- given
  (hstart : R.StartInteriorUnique h0) :
-- imply
  B.Fa = hexChi := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.Fa_eq_hexChi_of_startInteriorUnique hstart

/--
[normalized_contour_boundary_identity_of_startInteriorUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean)
-/
@[path]
private lemma normalized_contour_boundary_identity_of_startInteriorUnique_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
-- given
  (hstart : R.StartInteriorUnique h0) :
-- imply
  hexBdryCl * (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi) + hexBdryCt * (hexChi⁻¹ * (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi)) + hexChi⁻¹ * hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.normalized_contour_boundary_identity_of_startInteriorUnique hstart


-- created on 2026-10-23
