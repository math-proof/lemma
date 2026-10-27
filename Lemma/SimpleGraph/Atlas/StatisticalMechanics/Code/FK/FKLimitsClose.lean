import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
open MeasureTheory Filter Topology SimpleGraph Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[flc_vrad_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_vrad_le_eq
  {d : ℕ}
  {v : Site d}
  {i : Fin d} :
-- imply
  (v i).natAbs ≤ flc_vrad v := by
-- proof
  apply StatMech.FK.flc_vrad_le v i

/--
[flc_box_subset_transBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_box_subset_transBox_eq
  {d : ℕ}
  {v : Site d}
  {a m : ℕ}
-- given
  (hcm : a + flc_vrad v ≤ m) :
-- imply
  box d a ⊆ fvs_transBox d m v := by
-- proof
  apply StatMech.FK.flc_box_subset_transBox v hcm

/--
[flc_transBox_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_transBox_subset_box_eq
  {d : ℕ}
  {v : Site d}
  {m : ℕ} :
-- imply
  fvs_transBox d m v ⊆ box d (m + flc_vrad v) := by
-- proof
  apply StatMech.FK.flc_transBox_subset_box v m

/--
[flc_incl_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_incl_val_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (x : {y : Site d // y ∈ Sin}) :
-- imply
  (flc_incl hsub x : Site d) = (x : Site d) := by
-- proof
  apply StatMech.FK.flc_incl_val hsub x

/--
[flc_incl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_incl_injective_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
-- given
  (hsub : Sin ⊆ Sout) :
-- imply
  Function.Injective (flc_incl hsub) := by
-- proof
  apply StatMech.FK.flc_incl_injective hsub

/--
[flc_hbdryIn_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_hbdryIn_box_eq
  {d : ℕ}
  {a : ℕ}
  {z : Site d}
-- given
  (ha : 1 ≤ a)
  (x : {y : Site d // y ∈ box d a})
  (hnn : NearestNeighbour d (x : Site d) z)
  (hz : z ∉ box d a) :
-- imply
  boxBoundary d a x := by
-- proof
  apply StatMech.FK.flc_hbdryIn_box ha x z hnn hz

/--
[flc_hbdryIn_transBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_hbdryIn_transBox_eq
  {d : ℕ}
  {m : ℕ}
  {v : Site d}
  {z : Site d}
-- given
  (hm : 1 ≤ m)
  (x : {y : Site d // y ∈ fvs_transBox d m v})
  (hnn : NearestNeighbour d (x : Site d) z)
  (hz : z ∉ fvs_transBox d m v) :
-- imply
  fvs_transBoxBoundary d m v x := by
-- proof
  apply StatMech.FK.flc_hbdryIn_transBox hm v x z hnn hz

/--
[flc_hmargin_box_in_transBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_hmargin_box_in_transBox_eq
  {d : ℕ}
  {v : Site d}
  {a m : ℕ}
-- given
  (hsub : box d a ⊆ fvs_transBox d m v)
  (hcm : a + flc_vrad v + 1 ≤ m)
  (x : {y : Site d // y ∈ box d a}) :
-- imply
  ¬ fvs_transBoxBoundary d m v (flc_incl hsub x) := by
-- proof
  apply StatMech.FK.flc_hmargin_box_in_transBox v hsub hcm x

/--
[flc_hmargin_transBox_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_hmargin_transBox_in_box_eq
  {d : ℕ}
  {v : Site d}
  {m : ℕ}
-- given
  (hsub : fvs_transBox d m v ⊆ box d (m + flc_vrad v + 1))
  (x : {y : Site d // y ∈ fvs_transBox d m v}) :
-- imply
  ¬ boxBoundary d (m + flc_vrad v + 1) (flc_incl hsub x) := by
-- proof
  apply StatMech.FK.flc_hmargin_transBox_in_box v hsub x

/--
[flc_sym2map_val_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_sym2map_val_injective_eq
  {d : ℕ}
  {S : Set (Site d)} :
-- imply
  Function.Injective (Sym2.map (Subtype.val : {y : Site d // y ∈ S} → Site d)) := by
-- proof
  apply StatMech.FK.flc_sym2map_val_injective

/--
[flc_image_eq_of_val_image_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_image_eq_of_val_image_eq_eq
  {d : ℕ}
  {S : Set (Site d)}
  {F G : Finset (Sym2 {y : Site d // y ∈ S})}
-- given
  (h : F.image (Sym2.map (Subtype.val : {y : Site d // y ∈ S} → Site d)) = G.image (Sym2.map (Subtype.val : {y : Site d // y ∈ S} → Site d))) :
-- imply
  F = G := by
-- proof
  apply StatMech.FK.flc_image_eq_of_val_image_eq h

/--
[flc_valMap_ocd_innerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_valMap_ocd_innerEdge_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (e : Sym2 {y : Site d // y ∈ Sin}) :
-- imply
  Sym2.map (Subtype.val : {y : Site d // y ∈ Sout} → Site d) (ocd_innerEdge (flc_incl hsub) e) = Sym2.map (Subtype.val : {y : Site d // y ∈ Sin} → Site d) e := by
-- proof
  apply StatMech.FK.flc_valMap_ocd_innerEdge hsub e

/--
[flc_valImage_ocd_innerEdge_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_valImage_ocd_innerEdge_image_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
-- given
  (hsub : Sin ⊆ Sout)
  (F : Finset (Sym2 {y : Site d // y ∈ Sin})) :
-- imply
  (F.image (ocd_innerEdge (flc_incl hsub))).image (Sym2.map (Subtype.val : {y : Site d // y ∈ Sout} → Site d)) = F.image (Sym2.map (Subtype.val : {y : Site d // y ∈ Sin} → Site d)) := by
-- proof
  apply StatMech.FK.flc_valImage_ocd_innerEdge_image hsub F

/--
[flc_transBoxMass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_transBoxMass_eq_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
  {m : ℕ}
-- given
  (hNm : N ≤ m) :
-- imply
  lmc_transBoxMass v N t p m hNm = med_multiMassProb (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2) (flc_transEdges v N t m hNm) := by
-- proof
  apply StatMech.FK.flc_transBoxMass_eq v N t p m hNm

/--
[flc_valImage_transEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_valImage_transEdges_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {m : ℕ}
-- given
  (hNm : N ≤ m) :
-- imply
  (flc_transEdges v N t m hNm).image (Sym2.map (Subtype.val : fvs_transBoxVerts d m v → Site d)) = (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e) := by
-- proof
  apply StatMech.FK.flc_valImage_transEdges v N t m hNm

/--
[flc_centred_med_eq_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_centred_med_eq_measure_eq
  {d : ℕ}
  {n : ℕ}
  {tb : Finset (Sym2 (boxVerts d n))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  med_multiMassProb (wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) (boxBoundary d n) p 2) tb = (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (tb.image (edgeIncl d n))) := by
-- proof
  apply StatMech.FK.flc_centred_med_eq_measure n tb hp hp1

/--
[flc_squeeze_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_squeeze_lower_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
  {m : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hNm : N ≤ m)
  (hm : 1 ≤ m) :
-- imply
  (wiredFiniteMeasure d (m + flc_vrad v + 1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) ≤ lmc_transBoxMass v N t p m hNm := by
-- proof
  apply StatMech.FK.flc_squeeze_lower v N t hp hp1 m hNm hm

/--
[flc_squeeze_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_squeeze_upper_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
  {m a : ℕ}
  {tb_a : Finset (Sym2 (boxVerts d a))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hNm : N ≤ m)
  (ha : 1 ≤ a)
  (hcond : a + flc_vrad v + 1 ≤ m)
  (htb : tb_a.image (edgeIncl d a) = (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)) :
-- imply
  lmc_transBoxMass v N t p m hNm ≤ (wiredFiniteMeasure d a hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) := by
-- proof
  apply StatMech.FK.flc_squeeze_upper v N t hp hp1 m a hNm ha hcond tb_a htb

/--
[flc_transBoxMass_tendsto_translated_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_transBoxMass_tendsto_translated_iv_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m' : ℕ => lmc_transBoxMass v N t p (N + m') (Nat.le_add_right N m')) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))))) := by
-- proof
  apply StatMech.FK.flc_transBoxMass_tendsto_translated_iv v N t hp hp1

/--
[flc_wiredPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_wiredPlacement_eq
  {d : ℕ}
  {p : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  lmc_wiredPlacement hp hp1 g := by
-- proof
  apply StatMech.FK.flc_wiredPlacement hp hp1 g

/--
[flc_wiredPlacement_forall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_wiredPlacement_forall_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∀ g : Multiplicative (Site d), lmc_wiredPlacement hp hp1 g := by
-- proof
  apply StatMech.FK.flc_wiredPlacement_forall hp hp1

/--
[flc_wiredMultiHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_wiredMultiHomogeneous_eq
  {d : ℕ}
  {p : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  cdc_wiredMultiHomogeneous hp hp1 g := by
-- proof
  apply StatMech.FK.flc_wiredMultiHomogeneous hp hp1 g

/--
[flc_wiredIV_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean)
-/
@[path]
private lemma flc_wiredIV_isTranslationInvariant_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.flc_wiredIV_isTranslationInvariant hp hp1


-- created on 2026-10-23
