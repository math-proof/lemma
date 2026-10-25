import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.RosenfeldThroatClose.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[rtc_thickPoint_of_eastThroat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_thickPoint_of_eastThroat_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {e y : ℤ}
-- given
  (hcyc : Vc.IsCycle)
  (hE : (![e, y] : Site 2) ∈ Vc.support)
  (hSeed : (![e + 1, y] : Site 2) ∈ Vc.support)
  (hUp : (![e, y + 1] : Site 2) ∈ Vc.support)
  (hDn : (![e, y - 1] : Site 2) ∈ Vc.support) :
-- imply
  kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.rtc_thickPoint_of_eastThroat Vc hcyc hE hSeed hUp hDn

/--
[rtc_thickPoint_of_seedWall_nonConsec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_thickPoint_of_seedWall_nonConsec_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {e y : ℤ}
-- given
  (hE : (![e, y] : Site 2) ∈ Vc.support)
  (hSeed : (![e + 1, y] : Site 2) ∈ Vc.support)
  (hnon : s((![e, y] : Site 2), (![e + 1, y] : Site 2)) ∉ Vc.edges) :
-- imply
  kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.rtc_thickPoint_of_seedWall_nonConsec Vc hE hSeed hnon

/--
[rtc_thickPoint_of_upWall_nonConsec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_thickPoint_of_upWall_nonConsec_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {e y : ℤ}
-- given
  (hE : (![e, y] : Site 2) ∈ Vc.support)
  (hUp : (![e, y + 1] : Site 2) ∈ Vc.support)
  (hnon : s((![e, y] : Site 2), (![e, y + 1] : Site 2)) ∉ Vc.edges) :
-- imply
  kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.rtc_thickPoint_of_upWall_nonConsec Vc hE hUp hnon

/--
[rtc_eastThroat_discharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_eastThroat_discharge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {e y : ℤ}
-- given
  (hcyc : Vc.IsCycle)
  (hE : (![e, y] : Site 2) ∈ Vc.support)
  (hSeed : (![e + 1, y] : Site 2) ∈ Vc.support)
  (hUp : (![e, y + 1] : Site 2) ∈ Vc.support)
  (hSE : (![e, y - 1] : Site 2) ∈ Vc.support ∨ (![e, y - 1] : Site 2) ∉ jil_offSupportInterior Vc) :
-- imply
  kns_ThickPoint Vc ∨ ((![e, y - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧ (![e, y - 1] : Site 2) ∉ Vc.support ∧ s((![e, y] : Site 2), (![e + 1, y] : Site 2)) ∈ Vc.edges ∧ s((![e, y] : Site 2), (![e, y + 1] : Site 2)) ∈ Vc.edges) := by
-- proof
  apply StatMech.Lattice.rtc_eastThroat_discharge Vc hcyc hE hSeed hUp hSE

/--
[rtc_crossArcThick_of_pcy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_crossArcThick_of_pcy_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hpcy : pcy_CrossArcThick Vc seed) :
-- imply
  rtc_CrossArcThick Vc seed := by
-- proof
  apply StatMech.Lattice.rtc_crossArcThick_of_pcy Vc hpcy

/--
[rtc_crossArcThick_of_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_crossArcThick_of_crossArcThick_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hcat : cat_CrossArcThick Vc seed) :
-- imply
  rtc_CrossArcThick Vc seed := by
-- proof
  apply StatMech.Lattice.rtc_crossArcThick_of_crossArcThick Vc hcat

/--
[rtc_eastClause_discharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_eastClause_discharged_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {q : Site 2}
  {e : ℤ}
-- given
  (hcyc : Vc.IsCycle)
  (hE : (![e, q 1] : Site 2) ∈ Vc.support)
  (hSeed : (![e + 1, q 1] : Site 2) ∈ Vc.support)
  (hUp : (![e, q 1 + 1] : Site 2) ∈ Vc.support)
  (hSEclause : ((![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧ (![e, q 1 - 1] : Site 2) ∉ Vc.support) ∨ ((![e, q 1 - 1] : Site 2) ∈ Vc.support ∧ s((![e, q 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges ∧ s((![e - 1, q 1 - 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges)) :
-- imply
  kns_ThickPoint Vc ∨ ((![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧ (![e, q 1 - 1] : Site 2) ∉ Vc.support ∧ s((![e, q 1] : Site 2), (![e + 1, q 1] : Site 2)) ∈ Vc.edges ∧ s((![e, q 1] : Site 2), (![e, q 1 + 1] : Site 2)) ∈ Vc.edges) := by
-- proof
  apply StatMech.Lattice.rtc_eastClause_discharged Vc hcyc hE hSeed hUp hSEclause

/--
[rtc_fjord_eastThroat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_fjord_eastThroat_eq
-- given
  (hcyc : sdc_fjord.IsCycle) :
-- imply
  kns_ThickPoint sdc_fjord := by
-- proof
  apply StatMech.Lattice.rtc_fjord_eastThroat hcyc

/--
[rtc_fjord_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_fjord_crossArcThick_eq :
-- imply
  rtc_CrossArcThick sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.rtc_fjord_crossArcThick

/--
[rtc_fjord_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_fjord_nonvacuous_eq :
-- imply
  kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧ rtc_CrossArcThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord := by
-- proof
  apply StatMech.Lattice.rtc_fjord_nonvacuous

/--
[rtc_ksd_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_ksd_crossArcThick_eq :
-- imply
  rtc_CrossArcThick ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.rtc_ksd_crossArcThick

/--
[rtc_kda_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_kda_crossArcThick_eq :
-- imply
  rtc_CrossArcThick kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.rtc_kda_crossArcThick

/--
[rtc_kingRowLinked_of_fourThin_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_kingRowLinked_of_fourThin_cycle_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hcyc : Vc.IsCycle)
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hpcy : pcy_CrossArcThick Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.rtc_kingRowLinked_of_fourThin_cycle Vc hcyc hseedI hthin hpcy

/--
[rtc_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean)
-/
@[path]
private lemma rtc_summary_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hcyc : Vc.IsCycle)
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc) :
-- imply
  pcy_CrossArcThick Vc seed → rtc_CrossArcThick Vc seed ∧ mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.rtc_summary Vc hcyc hseedI hthin


-- created on 2026-10-23
