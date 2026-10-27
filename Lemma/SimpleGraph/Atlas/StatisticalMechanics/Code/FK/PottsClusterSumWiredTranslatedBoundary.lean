import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part6
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK


/--
[finiteConnToBdryEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma finiteConnToBdryEvent_isIncreasing_eq
  {G : SimpleGraph V}
  {x : V}
-- given
  (bdry : V -> Prop) :
-- imply
  IsIncreasing (finiteConnToBdryEvent G bdry x) := by
-- proof
  apply StatMech.FK.finiteConnToBdryEvent_isIncreasing G bdry x

/--
[wiredConnToBdryMass_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma wiredConnToBdryMass_equiv_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {sigma : V ≃ W}
  {p q : Real}
  {x : V}
-- given
  (bdryV : V -> Prop)
  (bdryW : W -> Prop)
  (hadj : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
  (hbdry : ∀ x, bdryV x ↔ bdryW (sigma x)) :
-- imply
  wiredConnToBdryMass H bdryW p q (sigma x) = wiredConnToBdryMass G bdryV p q x := by
-- proof
  apply StatMech.FK.wiredConnToBdryMass_equiv G H bdryV bdryW sigma hadj hbdry p q x

/--
[connToBdry_innerRestrict_of_connToBdry_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma connToBdry_innerRestrict_of_connToBdry_outer_eq
  {d : Nat}
  {Sin Sout : Set (Site d)}
  [Fintype Sin]
  [Fintype Sout]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {rho : ConfigSpace (Sym2 Sout)}
  {x : Sin}
-- given
  (hsub : Sin ⊆ Sout)
  (bdryOut : Sout -> Prop)
  (bdryIn : Sin -> Prop)
  (hmargin : ∀ x : Sin, ¬ bdryOut (flc_incl hsub x))
  (hbdryIn : ∀ (x : Sin) (z : Site d), NearestNeighbour d (x : Site d) z -> z ∉ Sin -> bdryIn x)
  (hout : ConnToBdry (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut rho (flc_incl hsub x)) :
-- imply
  ConnToBdry (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn (ocd_innerRestrict (flc_incl hsub) rho) x := by
-- proof
  apply StatMech.FK.connToBdry_innerRestrict_of_connToBdry_outer hsub bdryOut bdryIn hmargin hbdryIn rho x hout

/--
[wiredConnToBdryMass_outer_le_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma wiredConnToBdryMass_outer_le_inner_eq
  {d : Nat}
  {Sin Sout : Set (Site d)}
  [Fintype Sin]
  [Fintype Sout]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {p q : Real}
  {x : Sin}
-- given
  (hsub : Sin ⊆ Sout)
  (bdryOut : Sout -> Prop)
  (bdryIn : Sin -> Prop)
  (hmargin : ∀ x : Sin, ¬ bdryOut (flc_incl hsub x))
  (hbdryIn : ∀ (x : Sin) (z : Site d), NearestNeighbour d (x : Site d) z -> z ∉ Sin -> bdryIn x)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredConnToBdryMass (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut p q (flc_incl hsub x) ≤ wiredConnToBdryMass (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn p q x := by
-- proof
  apply StatMech.FK.wiredConnToBdryMass_outer_le_inner hsub bdryOut bdryIn hmargin hbdryIn hp hp1 hq x

/--
[transBoxCenter_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma transBoxCenter_val_eq
  {d n : Nat}
  {x : Site d} :
-- imply
  (transBoxCenter d n x : Site d) = x := by
-- proof
  apply StatMech.FK.transBoxCenter_val d n x

/--
[translated_wiredConnToBdryMass_eq_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma translated_wiredConnToBdryMass_eq_centered_eq
  {d : Nat}
  {x : Site d}
  {n : Nat}
  {p q : Real} :
-- imply
  wiredConnToBdryMass (fvs_transBoxGraph d n x) (fvs_transBoxBoundary d n x) p q (transBoxCenter d n x) = wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q (boxOrigin d n) := by
-- proof
  apply StatMech.FK.translated_wiredConnToBdryMass_eq_centered x n p q

/--
[translated_outer_boundaryMass_le_centered_marked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma translated_outer_boundaryMass_le_centered_marked_eq
  {d : Nat}
  {x : Site d}
  {n : Nat}
  {p q : Real}
-- given
  (hn : 1 ≤ n)
  (hxn : flc_vrad x ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredConnToBdryMass (fvs_transBoxGraph d (n + flc_vrad x + 1) x) (fvs_transBoxBoundary d (n + flc_vrad x + 1) x) p q (transBoxCenter d (n + flc_vrad x + 1) x) ≤ wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q ⟨x, by exact fun i => (flc_vrad_le x i).trans hxn⟩ := by
-- proof
  apply StatMech.FK.translated_outer_boundaryMass_le_centered_marked x n hn hxn hp hp1 hq

/--
[centered_marked_boundaryMass_le_translated_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma centered_marked_boundaryMass_le_translated_inner_eq
  {d : Nat}
  {x : Site d}
  {n : Nat}
  {p q : Real}
-- given
  (hn : 1 ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredConnToBdryMass (boxGraph d (n + flc_vrad x + 1)) (boxBoundary d (n + flc_vrad x + 1)) p q ⟨x, box_mono d (by omega) (fun i => flc_vrad_le x i)⟩ ≤ wiredConnToBdryMass (fvs_transBoxGraph d n x) (fvs_transBoxBoundary d n x) p q (transBoxCenter d n x) := by
-- proof
  apply StatMech.FK.centered_marked_boundaryMass_le_translated_inner x n hn hp hp1 hq

/--
[boxMarkedVertex_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma boxMarkedVertex_eq_of_mem_eq
  {d n : Nat}
  {x : Site d}
-- given
  (hx : x ∈ box d n) :
-- imply
  boxMarkedVertex d n x = ⟨x, hx⟩ := by
-- proof
  apply StatMech.FK.boxMarkedVertex_eq_of_mem hx

/--
[centeredMarkedBoundaryMass_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma centeredMarkedBoundaryMass_eq_of_mem_eq
  {d n : Nat}
  {x : Site d}
  {p q : Real}
-- given
  (hx : x ∈ box d n) :
-- imply
  centeredMarkedBoundaryMass d x n p q = wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q ⟨x, hx⟩ := by
-- proof
  apply StatMech.FK.centeredMarkedBoundaryMass_eq_of_mem hx p q

/--
[centered_origin_wiredConnToBdryMass_eq_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma centered_origin_wiredConnToBdryMass_eq_measure_eq
  {d n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q (boxOrigin d n) = (wiredFiniteMeasure d n hp hp1 hq : Measure _).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.centered_origin_wiredConnToBdryMass_eq_measure hp hp1 hq

/--
[centered_origin_wiredConnToBdryMass_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma centered_origin_wiredConnToBdryMass_tendsto_eq
  {d : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q (boxOrigin d n)) atTop (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
-- proof
  apply StatMech.FK.centered_origin_wiredConnToBdryMass_tendsto hp hp1 hq

/--
[centeredMarkedBoundaryMass_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma centeredMarkedBoundaryMass_tendsto_eq
  {d : Nat}
  {x : Site d}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => centeredMarkedBoundaryMass d x n p q) atTop (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
-- proof
  apply StatMech.FK.centeredMarkedBoundaryMass_tendsto x hp hp1 hq

/--
[shift_preimage_clusterInfiniteEvent_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma shift_preimage_clusterInfiniteEvent_wired_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {x : Site d} :
-- imply
  (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) -> _) ⁻¹' clusterInfiniteEvent d (g • x) = clusterInfiniteEvent d x := by
-- proof
  apply StatMech.FK.shift_preimage_clusterInfiniteEvent_wired g x

/--
[wiredInfiniteVolume_clusterInfiniteEvent_real_eq_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma wiredInfiniteVolume_clusterInfiniteEvent_real_eq_fkTheta_eq
  {d : Nat}
  {x : Site d}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (clusterInfiniteEvent d x) = fkTheta d hp hp1 (zero_lt_one.trans_le hq) := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_clusterInfiniteEvent_real_eq_fkTheta x hp hp1 hq

/--
[wiredOpenExterior_clusterInfiniteEvent_real_eq_centeredMarkedBoundaryMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma wiredOpenExterior_clusterInfiniteEvent_real_eq_centeredMarkedBoundaryMass_eq
  {d n : Nat}
  {x : Site d}
  {p q : Real}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n)
  (hx : x ∈ box d n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (wiredOpenExteriorFiniteMeasure d n hp hp1 hq : Measure _).real (clusterInfiniteEvent d x) = centeredMarkedBoundaryMass d x n p q := by
-- proof
  apply StatMech.FK.wiredOpenExterior_clusterInfiniteEvent_real_eq_centeredMarkedBoundaryMass hd hn x hx hp hp1 hq

/--
[wiredOpenExterior_clusterInfiniteEvent_real_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma wiredOpenExterior_clusterInfiniteEvent_real_tendsto_eq
  {d : Nat}
  {x : Site d}
  {p q : Real}
-- given
  (hd : 2 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => (wiredOpenExteriorFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (clusterInfiniteEvent d x)) atTop (nhds ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (clusterInfiniteEvent d x))) := by
-- proof
  apply StatMech.FK.wiredOpenExterior_clusterInfiniteEvent_real_tendsto hd x hp hp1 hq

/--
[wiredTruncatedInfiniteEvent_eq_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma wiredTruncatedInfiniteEvent_eq_preimage_eq
  {d R : Nat}
  {x : Site d}
-- given
  (hd : 2 ≤ d)
  (hR : 1 ≤ R)
  (hx : x ∈ box d R) :
-- imply
  wiredTruncatedInfiniteEvent d R x = boxRestrict d R ⁻¹' finiteConnToBdryEvent (boxGraph d R) (boxBoundary d R) ⟨x, hx⟩ := by
-- proof
  apply StatMech.FK.wiredTruncatedInfiniteEvent_eq_preimage hd hR x hx

/--
[isClopen_wiredTruncatedInfiniteEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma isClopen_wiredTruncatedInfiniteEvent_eq
  {d R : Nat}
  {x : Site d}
-- given
  (hd : 2 ≤ d)
  (hR : 1 ≤ R)
  (hx : x ∈ box d R) :
-- imply
  IsClopen (wiredTruncatedInfiniteEvent d R x) := by
-- proof
  apply StatMech.FK.isClopen_wiredTruncatedInfiniteEvent hd hR x hx

/--
[measurableSet_wiredTruncatedInfiniteEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean)
-/
@[path]
private lemma measurableSet_wiredTruncatedInfiniteEvent_eq
  {d R : Nat}
  {x : Site d}
-- given
  (hd : 2 ≤ d)
  (hR : 1 ≤ R)
  (hx : x ∈ box d R) :
-- imply
  MeasurableSet (wiredTruncatedInfiniteEvent d R x) := by
-- proof
  apply StatMech.FK.measurableSet_wiredTruncatedInfiniteEvent hd hR x hx


-- created on 2026-10-23
