import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.LimitCommutation.Part5
open MeasureTheory Filter Topology SimpleGraph Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[lmc_transEdgeIncl_sigma_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_transEdgeIncl_sigma_eq_smul_eq
  {d : ℕ}
  {d m : ℕ}
  {v : Site d}
  {eb : Sym2 (boxVerts d m)} :
-- imply
  lmc_transEdgeIncl d m v (Sym2.map (fvs_transEquiv d m v) eb) = (Multiplicative.ofAdd v) • (edgeIncl d m eb) := by
-- proof
  apply StatMech.FK.lmc_transEdgeIncl_sigma_eq_smul d m v eb

/--
[lmc_transImage_eq_smulImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_transImage_eq_smulImage_eq
  {d : ℕ}
  {d m : ℕ}
  {v : Site d}
  {t : Finset (Sym2 (boxVerts d m))} :
-- imply
  (t.image (Sym2.map (fvs_transEquiv d m v))).image (lmc_transEdgeIncl d m v) = (t.image (edgeIncl d m)).image (fun e => (Multiplicative.ofAdd v) • e) := by
-- proof
  apply StatMech.FK.lmc_transImage_eq_smulImage d m v t

/--
[lmc_transBoxMass_eq_centred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_transBoxMass_eq_centred_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
  {m : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hNm : N ≤ m) :
-- imply
  lmc_transBoxMass v N t p m hNm = (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
-- proof
  apply StatMech.FK.lmc_transBoxMass_eq_centred v N t hp hp1 m hNm

/--
[lmc_transBoxMass_tendsto_centred_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_transBoxMass_tendsto_centred_iv_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m)) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
-- proof
  apply StatMech.FK.lmc_transBoxMass_tendsto_centred_iv v N t hp hp1

/--
[lmc_wiredMultiHomogeneous_of_cofinal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_wiredMultiHomogeneous_of_cofinal_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcofinal : Tendsto (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m)) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)))))) :
-- imply
  (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) := by
-- proof
  apply StatMech.FK.lmc_wiredMultiHomogeneous_of_cofinal v N t hp hp1 hcofinal

/--
[lmc_wiredMultiHomogeneous_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_wiredMultiHomogeneous_of_decay_eq
  {d : ℕ}
  {v : Site d}
  {N N' : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {t' : Finset (Sym2 (boxVerts d N'))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hst' : (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e) = t'.image (edgeIncl d N'))
  (hdecay : Tendsto (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m) - (wiredFiniteMeasure d (N' + m) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t'.image (edgeIncl d N')))) atTop (𝓝 0)) :
-- imply
  (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) := by
-- proof
  apply StatMech.FK.lmc_wiredMultiHomogeneous_of_decay v N N' t t' hp hp1 hst' hdecay

/--
[lmc_wiredMultiHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_wiredMultiHomogeneous_eq
  {d : ℕ}
  {p : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hplace : lmc_wiredPlacement hp hp1 g) :
-- imply
  cdc_wiredMultiHomogeneous hp hp1 g := by
-- proof
  apply StatMech.FK.lmc_wiredMultiHomogeneous hp hp1 g hplace

/--
[lmc_wiredPlacement_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_wiredPlacement_one_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  lmc_wiredPlacement hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.lmc_wiredPlacement_one hp hp1

/--
[lmc_wiredMultiHomogeneous_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_wiredMultiHomogeneous_one_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  cdc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.lmc_wiredMultiHomogeneous_one hp hp1

/--
[lmc_wiredIV_isTranslationInvariant_of_placement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_wiredIV_isTranslationInvariant_of_placement_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hplace : ∀ g : Multiplicative (Site d), lmc_wiredPlacement hp hp1 g) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.lmc_wiredIV_isTranslationInvariant_of_placement hp hp1 hplace

/--
[lmc_transBoxMassFree_eq_centred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_transBoxMassFree_eq_centred_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
  {m : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hNm : N ≤ m) :
-- imply
  lmc_transBoxMassFree v N t p m hNm = (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
-- proof
  apply StatMech.FK.lmc_transBoxMassFree_eq_centred v N t hp hp1 m hNm

/--
[lmc_transBoxMassFree_tendsto_centred_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_transBoxMassFree_tendsto_centred_iv_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m : ℕ => lmc_transBoxMassFree v N t p (N + m) (Nat.le_add_right N m)) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
-- proof
  apply StatMech.FK.lmc_transBoxMassFree_tendsto_centred_iv v N t hp hp1

/--
[lmc_freeMultiHomogeneous_of_cofinal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_freeMultiHomogeneous_of_cofinal_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcofinal : Tendsto (fun m : ℕ => lmc_transBoxMassFree v N t p (N + m) (Nat.le_add_right N m)) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)))))) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) := by
-- proof
  apply StatMech.FK.lmc_freeMultiHomogeneous_of_cofinal v N t hp hp1 hcofinal

/--
[lmc_freeMultiHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_freeMultiHomogeneous_eq
  {d : ℕ}
  {p : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hplace : lmc_freePlacement hp hp1 g) :
-- imply
  cdc_freeMultiHomogeneous hp hp1 g := by
-- proof
  apply StatMech.FK.lmc_freeMultiHomogeneous hp hp1 g hplace

/--
[lmc_freePlacement_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_freePlacement_one_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  lmc_freePlacement hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.lmc_freePlacement_one hp hp1

/--
[lmc_freeMultiHomogeneous_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_freeMultiHomogeneous_one_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  cdc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.lmc_freeMultiHomogeneous_one hp hp1

/--
[lmc_freeIV_isTranslationInvariant_of_placement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean)
-/
@[path]
private lemma lmc_freeIV_isTranslationInvariant_of_placement_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hplace : ∀ g : Multiplicative (Site d), lmc_freePlacement hp hp1 g) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.lmc_freeIV_isTranslationInvariant_of_placement hp hp1 hplace


-- created on 2026-10-23
