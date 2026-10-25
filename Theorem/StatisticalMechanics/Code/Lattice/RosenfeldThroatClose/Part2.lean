/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.KingStepConnectClose
import Theorem.StatisticalMechanics.Code.Lattice.KingNoSeparationClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EscapeThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EscapeWallThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GlobalThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossArcThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingPinchClose
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsCycleClose.Part3
import Def.StatisticalMechanics.Code.Lattice.RosenfeldThroatClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem rtc_crossArcThick_of_pcy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hpcy : pcy_CrossArcThick Vc seed) : rtc_CrossArcThick Vc seed := by
  intro hcyc T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hSWclause hbottom
    e he₁ he₂ he₃ hbotCorner _hSeed _hUp hSEclause
  exact hpcy hcyc T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hSWclause hbottom
    e he₁ he₂ he₃ hbotCorner hSEclause


theorem rtc_crossArcThick_of_crossArcThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hcat : cat_CrossArcThick Vc seed) : rtc_CrossArcThick Vc seed := by
  intro _hcyc T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hSWclause hbottom
    e he₁ he₂ he₃ hbotCorner _hSeed _hUp hSEclause
  exact hcat T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hSWclause hbottom
    e he₁ he₂ he₃ hbotCorner hSEclause


theorem rtc_eastClause_discharged {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) {q : Site 2} {e : ℤ}
    (hE : (![e, q 1] : Site 2) ∈ Vc.support)
    (hSeed : (![e + 1, q 1] : Site 2) ∈ Vc.support)
    (hUp : (![e, q 1 + 1] : Site 2) ∈ Vc.support)
    (hSEclause :
      ((![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![e, q 1 - 1] : Site 2) ∉ Vc.support) ∨
      ((![e, q 1 - 1] : Site 2) ∈ Vc.support ∧
        s((![e, q 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges ∧
        s((![e - 1, q 1 - 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges)) :
    kns_ThickPoint Vc ∨
      ((![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![e, q 1 - 1] : Site 2) ∉ Vc.support ∧
        s((![e, q 1] : Site 2), (![e + 1, q 1] : Site 2)) ∈ Vc.edges ∧
        s((![e, q 1] : Site 2), (![e, q 1 + 1] : Site 2)) ∈ Vc.edges) := by
  have hSE : (![e, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
    rcases hSEclause with ⟨hext, _⟩ | ⟨hsup, _, _⟩
    · exact Or.inr hext
    · exact Or.inl hsup
  exact rtc_eastThroat_discharge Vc hcyc hE hSeed hUp hSE


theorem rtc_fjord_eastThroat (hcyc : sdc_fjord.IsCycle) : kns_ThickPoint sdc_fjord := by
  obtain ⟨h31, _, _, _, h30, h32, h41, _, _, _⟩ := pcy_fjord_throat_three_neighbors
  exact rtc_thickPoint_of_eastThroat sdc_fjord hcyc (e := 3) (y := 1) h31 h41 h32 h30


theorem rtc_fjord_crossArcThick : rtc_CrossArcThick sdc_fjord (![5, 1] : Site 2) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact kns_fjord_thickPoint


theorem rtc_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    rtc_CrossArcThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, rtc_fjord_crossArcThick,
   mci_fjord_not_fourThin⟩


theorem rtc_ksd_crossArcThick : rtc_CrossArcThick ksd_stair (![1, 1] : Site 2) :=
  rtc_crossArcThick_of_crossArcThick ksd_stair cat_ksd_crossArcThick


theorem rtc_kda_crossArcThick : rtc_CrossArcThick kda_stairDR (![3, 1] : Site 2) :=
  rtc_crossArcThick_of_crossArcThick kda_stairDR cat_kda_crossArcThick


theorem rtc_kingRowLinked_of_fourThin_cycle {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hcyc : Vc.IsCycle) (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hthin : mci_FourThin Vc) (hpcy : pcy_CrossArcThick Vc seed) :
    mci_KingRowLinked Vc seed :=
  pcy_kingRowLinked_of_fourThin_cycle Vc hcyc hseedI hthin hpcy


theorem rtc_summary {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hcyc : Vc.IsCycle) (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc) :
    pcy_CrossArcThick Vc seed → rtc_CrossArcThick Vc seed ∧ mci_KingRowLinked Vc seed :=
  fun hpcy => ⟨rtc_crossArcThick_of_pcy Vc hpcy,
    rtc_kingRowLinked_of_fourThin_cycle Vc hcyc hseedI hthin hpcy⟩

end Lattice
end StatMech
