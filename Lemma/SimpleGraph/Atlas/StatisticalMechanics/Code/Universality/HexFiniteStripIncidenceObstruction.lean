import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part4
open StatMech StatMech.Universality


/--
[hexContourSum_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma hexContourSum_empty_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  hexContourSum inRegion a h0 ∅ x = 0 := by
-- proof
  apply StatMech.Universality.hexContourSum_empty inRegion a h0 x

/--
[hexContourFamily_singleton_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma hexContourFamily_singleton_start_eq
  {a : ℂ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hreg : inRegion a) :
-- imply
  hexContourFamily inRegion a h0 ({a} : Set ℂ) = {[]} := by
-- proof
  apply StatMech.Universality.hexContourFamily_singleton_start inRegion a h0 hreg

/--
[hexContourSum_singleton_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma hexContourSum_singleton_start_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hreg : inRegion a) :
-- imply
  hexContourSum inRegion a h0 ({a} : Set ℂ) x = x := by
-- proof
  apply StatMech.Universality.hexContourSum_singleton_start inRegion a h0 x hreg

/--
[hexEmptyIncidenceDomain_incidences](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma hexEmptyIncidenceDomain_incidences_eq
  {R : HexFiniteRegion}
-- given
  (h0 : ℤ) :
-- imply
  (hexEmptyIncidenceDomain R h0).incidences = ∅ := by
-- proof
  apply StatMech.Universality.hexEmptyIncidenceDomain_incidences R h0

/--
[hexEmptyIncidenceBoundaryData_no_incidences](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma hexEmptyIncidenceBoundaryData_no_incidences_eq
  {R : HexFiniteRegion}
-- given
  (h0 : ℤ) :
-- imply
  (hexEmptyIncidenceDomain R h0).incidences = ∅ := by
-- proof
  apply StatMech.Universality.hexEmptyIncidenceBoundaryData_no_incidences R h0

/--
[hexEmptyIncidenceBoundaryData_topContour_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma hexEmptyIncidenceBoundaryData_topContour_eq_eq
  {R : HexFiniteRegion}
-- given
  (h0 : ℤ) :
-- imply
  hexContourUpsilon R.inRegion R.start h0 (hexEmptyIncidenceBoundaryData R h0).sides hexChi = hexChi := by
-- proof
  apply StatMech.Universality.hexEmptyIncidenceBoundaryData_topContour_eq R h0

/--
[hexEmptyIncidenceBoundaryData_topContour_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma hexEmptyIncidenceBoundaryData_topContour_ne_zero_eq
  {R : HexFiniteRegion}
-- given
  (h0 : ℤ) :
-- imply
  hexContourUpsilon R.inRegion R.start h0 (hexEmptyIncidenceBoundaryData R h0).sides hexChi ≠ 0 := by
-- proof
  apply StatMech.Universality.hexEmptyIncidenceBoundaryData_topContour_ne_zero R h0

/--
[hexEmptyIncidenceBoundaryData_not_enumerated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma hexEmptyIncidenceBoundaryData_not_enumerated_eq
  {R : HexFiniteRegion}
-- given
  (h0 : ℤ) :
-- imply
  ¬ Nonempty (HexFiniteStripIncidenceEnumeration (hexEmptyIncidenceBoundaryData R h0)) := by
-- proof
  apply StatMech.Universality.hexEmptyIncidenceBoundaryData_not_enumerated R h0

/--
[HexPhaseData.startFiber_nonempty_of_Fa_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma startFiber_nonempty_of_Fa_ne_zero_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {G : HexRegion}
  {H : HexPhaseData D P G}
-- given
  (hFa : H.Fa ≠ 0) :
-- imply
  ((D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0)).Nonempty := by
-- proof
  apply StatMech.Universality.HexPhaseData.startFiber_nonempty_of_Fa_ne_zero H hFa

/--
[HexPhaseData.Fa_eq_zero_of_startFiber_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma Fa_eq_zero_of_startFiber_singleton_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {G : HexRegion}
  {H : HexPhaseData D P G}
  {eA : HexIncidence V}
-- given
  (hfiber : (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0) = {eA})
  (hmid : D.mid eA.vtx eA.edge = G.start)
  (hobs : D.obs G.start = (H.Fa : ℂ)) :
-- imply
  H.Fa = 0 := by
-- proof
  apply StatMech.Universality.HexPhaseData.Fa_eq_zero_of_startFiber_singleton H eA hfiber hmid hobs

/--
[HexPhaseData.not_startFiber_singleton_of_Fa_eq_hexChi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma not_startFiber_singleton_of_Fa_eq_hexChi_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {G : HexRegion}
  {H : HexPhaseData D P G}
  {eA : HexIncidence V}
-- given
  (hfiber : (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0) = {eA})
  (hmid : D.mid eA.vtx eA.edge = G.start)
  (hobs : D.obs G.start = (H.Fa : ℂ))
  (hFa : H.Fa = hexChi) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.HexPhaseData.not_startFiber_singleton_of_Fa_eq_hexChi H eA hfiber hmid hobs hFa

/--
[HexFiniteStripBoundaryData.phaseA_startFiber_card_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma phaseA_startFiber_card_ne_one_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {G : HexRegion}
  {B : HexFiniteStripBoundaryData R h0 D P}
  {H : HexPhaseData D P G}
-- given
  (hstart : G.start = R.start)
  (hFa : H.Fa = B.Fa)
  (hmid : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0), D.mid e.vtx e.edge = G.start) :
-- imply
  ((D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0)).card ≠ 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.phaseA_startFiber_card_ne_one B H hstart hFa hmid

/--
[HexFiniteStripBoundaryData.two_le_phaseA_startFiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean)
-/
@[path]
private lemma two_le_phaseA_startFiber_card_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {G : HexRegion}
  {B : HexFiniteStripBoundaryData R h0 D P}
  {H : HexPhaseData D P G}
-- given
  (hstart : G.start = R.start)
  (hFa : H.Fa = B.Fa)
  (hmid : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0), D.mid e.vtx e.edge = G.start) :
-- imply
  2 ≤ ((D.incidences \ P.interior).filter (fun e => hexRegionClsInc G D e = 0)).card := by
-- proof
  apply StatMech.Universality.HexFiniteStripBoundaryData.two_le_phaseA_startFiber_card B H hstart hFa hmid


-- created on 2026-10-23
