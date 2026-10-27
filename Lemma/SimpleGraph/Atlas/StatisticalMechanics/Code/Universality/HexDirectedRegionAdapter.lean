import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter.Part6
open StatMech StatMech.Universality


/--
[hexStripInterior_of_headingPeriodic_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexStripInterior_of_headingPeriodic_edge_eq
  {m : ℂ}
-- given
  (dregion : ℂ → ℤ → Prop)
  (hperiodic : HexHeadingPeriodic dregion)
  (h : ℤ)
  (hmh : dregion m h) :
-- imply
  hexStripInterior dregion (m + halfStep h) ∧ hexStripInterior dregion (m + halfStep (h + 3)) := by
-- proof
  apply StatMech.Universality.hexStripInterior_of_headingPeriodic_edge dregion hperiodic m h hmh

/--
[not_hexStrip_uniqueInterior_of_headingPeriodic_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma not_hexStrip_uniqueInterior_of_headingPeriodic_start_eq
  {a : ℂ}
-- given
  (dregion : ℂ → ℤ → Prop)
  (h0 : ℤ)
  (hperiodic : HexHeadingPeriodic dregion)
  (hstart : dregion a h0) :
-- imply
  ¬(∀ h : ℤ, hexStripInterior dregion (a + halfStep h) → halfStep h = halfStep h0) := by
-- proof
  apply StatMech.Universality.not_hexStrip_uniqueInterior_of_headingPeriodic_start dregion a h0 hperiodic hstart

/--
[hexStripDirMids_fst_mem_midsAux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexStripDirMids_fst_mem_midsAux_eq
  {m : ℂ}
  {ts : List ℤ}
  {p : ℂ × ℤ}
-- given
  (h : ℤ)
  (hp : p ∈ hexStripDirMids m h ts) :
-- imply
  p.1 ∈ midsAux m h ts := by
-- proof
  apply StatMech.Universality.hexStripDirMids_fst_mem_midsAux m h ts p hp

/--
[hexStripMembershipDRegion_staysInDir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexStripMembershipDRegion_staysInDir_eq
  {M : Finset ℂ}
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hstay : (ofTurns a h0 ts).StaysIn (fun m => m ∈ M)) :
-- imply
  hexStripStaysInDir (hexStripMembershipDRegion M) a h0 ts := by
-- proof
  apply StatMech.Universality.hexStripMembershipDRegion_staysInDir M a h0 ts hstay

/--
[hexStripMembershipDRegion_headingPeriodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexStripMembershipDRegion_headingPeriodic_eq
  {M : Finset ℂ} :
-- imply
  HexHeadingPeriodic (hexStripMembershipDRegion M) := by
-- proof
  apply StatMech.Universality.hexStripMembershipDRegion_headingPeriodic M

/--
[hexStripMembershipDRegion_not_uniqueInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexStripMembershipDRegion_not_uniqueInterior_eq
  {M : Finset ℂ}
  {a : ℂ}
-- given
  (ha : a ∈ M)
  (h0 : ℤ) :
-- imply
  ¬(∀ h : ℤ, hexStripInterior (hexStripMembershipDRegion M) (a + halfStep h) → halfStep h = halfStep h0) := by
-- proof
  apply StatMech.Universality.hexStripMembershipDRegion_not_uniqueInterior M a ha h0

/--
[hexReturning_staysInDir_of_launch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexReturning_staysInDir_of_launch_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (dregion : ℂ → ℤ → Prop)
  (h0 : ℤ)
  (hlaunch : dregion a h0)
  (hlegal : (ofTurns a h0 ts).IsLegalSAW)
  (hend : (ofTurns a h0 ts).EndsAt a) :
-- imply
  hexStripStaysInDir dregion a h0 ts := by
-- proof
  apply StatMech.Universality.hexReturning_staysInDir_of_launch dregion a h0 hlaunch ts hlegal hend

/--
[hexStripInterior_of_distinctMidpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexStripInterior_of_distinctMidpoint_eq
  {v : ℂ}
-- given
  (dregion : ℂ → ℤ → Prop)
  (hv : hexStripInteriorDistinctMidpoint dregion v) :
-- imply
  hexStripInterior dregion v := by
-- proof
  apply StatMech.Universality.hexStripInterior_of_distinctMidpoint dregion v hv

/--
[hexStrip_interiorVertices_distinctMidpoint_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexStrip_interiorVertices_distinctMidpoint_core_eq
  {a : ℂ}
  {ts : List ℤ}
  {v : ℂ}
-- given
  (dregion : ℂ → ℤ → Prop)
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).IsLegalSAW)
  (hstay : hexStripStaysInDir dregion a h0 ts)
  (hv : v ∈ (ofTurns a h0 ts).vertices)
  (hvne : v ≠ hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts)) :
-- imply
  hexStripInteriorDistinctMidpoint dregion v := by
-- proof
  apply StatMech.Universality.hexStrip_interiorVertices_distinctMidpoint_core dregion a h0 ts hlegal hstay v hv hvne

/--
[hexDomainInwardDRegion_headingPeriodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexDomainInwardDRegion_headingPeriodic_eq
  [DecidableEq V]
  {D : HexDomain V} :
-- imply
  HexHeadingPeriodic (hexDomainInwardDRegion D) := by
-- proof
  apply StatMech.Universality.hexDomainInwardDRegion_headingPeriodic D

/--
[hexDomainInwardDRegion_project](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexDomainInwardDRegion_project_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexFiniteStripBoundaryData R h0 D P}
  {m : ℂ}
-- given
  (h : ℤ)
  (hm : hexDomainInwardDRegion D m h) :
-- imply
  R.inRegion m := by
-- proof
  apply StatMech.Universality.hexDomainInwardDRegion_project B m h hm

/--
[hexDomainInwardDRegion_not_old_uniqueInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean)
-/
@[path]
private lemma hexDomainInwardDRegion_not_old_uniqueInterior_eq
  [DecidableEq V]
  {D : HexDomain V}
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hstart : hexDomainInwardDRegion D a h0) :
-- imply
  ¬(∀ h : ℤ, hexStripInterior (hexDomainInwardDRegion D) (a + halfStep h) → halfStep h = halfStep h0) := by
-- proof
  apply StatMech.Universality.hexDomainInwardDRegion_not_old_uniqueInterior D a h0 hstart


-- created on 2026-10-23
