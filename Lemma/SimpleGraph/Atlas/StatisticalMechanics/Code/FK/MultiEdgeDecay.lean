import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.MultiEdgeDecay
open MeasureTheory Filter Topology SimpleGraph Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[med_boxMultiOpenEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_boxMultiOpenEvent_eq_eq
  {d : ℕ}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))} :
-- imply
  cdc_boxMultiOpenEvent N t = med_genericMultiOpenEvent t := by
-- proof
  apply StatMech.FK.med_boxMultiOpenEvent_eq N t

/--
[med_genericMultiOpenEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_genericMultiOpenEvent_increasing_eq
  {d : ℕ}
  {t : Finset (Sym2 V)} :
-- imply
  IsIncreasing (med_genericMultiOpenEvent t) := by
-- proof
  apply StatMech.FK.med_genericMultiOpenEvent_increasing t

/--
[med_reCfgIso_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_reCfgIso_preimage_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {σ : V ≃ W}
  {t : Finset (Sym2 V)} :
-- imply
  reCfgIso σ ⁻¹' (med_genericMultiOpenEvent t) = med_genericMultiOpenEvent (t.image (Sym2.map σ)) := by
-- proof
  apply StatMech.FK.med_reCfgIso_preimage σ t

/--
[med_centred_mass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_centred_mass_eq_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {m : ℕ}
  {t : Finset (Sym2 (boxVerts d m))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d m))) = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) t := by
-- proof
  apply StatMech.FK.med_centred_mass_eq m t hp hp1

/--
[med_free_centred_mass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_free_centred_mass_eq_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {m : ℕ}
  {t : Finset (Sym2 (boxVerts d m))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d m))) = med_multiMassProb (fkProb (boxGraph d m) p 2) t := by
-- proof
  apply StatMech.FK.med_free_centred_mass_eq m t hp hp1

/--
[med_centred_eq_translated_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_centred_eq_translated_wired_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {m : ℕ}
  {v : Site d}
  {t : Finset (Sym2 (boxVerts d m))}
  {p : ℝ} :
-- imply
  med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) t = med_multiMassProb (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2) (t.image (Sym2.map (fvs_transEquiv d m v))) := by
-- proof
  apply StatMech.FK.med_centred_eq_translated_wired m v t

/--
[med_centred_eq_translated_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_centred_eq_translated_free_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {m : ℕ}
  {v : Site d}
  {t : Finset (Sym2 (boxVerts d m))}
  {p : ℝ} :
-- imply
  med_multiMassProb (fkProb (boxGraph d m) p 2) t = med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2) (t.image (Sym2.map (fvs_transEquiv d m v))) := by
-- proof
  apply StatMech.FK.med_centred_eq_translated_free m v t

/--
[med_centred_tendsto_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_centred_tendsto_iv_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
-- proof
  apply StatMech.FK.med_centred_tendsto_iv N t hp hp1

/--
[med_free_centred_tendsto_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_free_centred_tendsto_iv_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
-- proof
  apply StatMech.FK.med_free_centred_tendsto_iv N t hp hp1

/--
[med_edgeIncl_innerEdgeLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_edgeIncl_innerEdgeLE_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {N m : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hNm : N ≤ m) :
-- imply
  edgeIncl d m (innerEdgeLE d hNm eb) = edgeIncl d N eb := by
-- proof
  apply StatMech.FK.med_edgeIncl_innerEdgeLE N m hNm eb

/--
[med_multiEvent_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_multiEvent_lift_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {N m : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
-- given
  (hNm : N ≤ m) :
-- imply
  cdc_multiOpenEvent ((t.image (innerEdgeLE d hNm)).image (edgeIncl d m)) = cdc_multiOpenEvent (t.image (edgeIncl d N)) := by
-- proof
  apply StatMech.FK.med_multiEvent_lift N m hNm t

/--
[med_centred_mass_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_centred_mass_lift_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {N m : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (t.image (innerEdgeLE d hNm)) := by
-- proof
  apply StatMech.FK.med_centred_mass_lift N m hNm t hp hp1

/--
[med_offCentreMultiCarrier_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_offCentreMultiCarrier_eq_zero_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
  {m : ℕ}
-- given
  (hNm : N ≤ m) :
-- imply
  med_offCentreMultiCarrier v N t p m hNm = 0 := by
-- proof
  apply StatMech.FK.med_offCentreMultiCarrier_eq_zero v N t p m hNm

/--
[med_offCentreMultiCarrier_squeeze](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_offCentreMultiCarrier_squeeze_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ} :
-- imply
  Tendsto (fun m : ℕ => med_offCentreMultiCarrier v N t p (N + m) (Nat.le_add_right N m)) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.med_offCentreMultiCarrier_squeeze v N t p

/--
[med_wiredMultiHomogeneous_of_cofinal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_wiredMultiHomogeneous_of_cofinal_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {v : Site d}
  {N : ℕ}
  {t t' : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (htrans : ∀ᶠ m in atTop, ∀ (hNm : N ≤ m), med_multiMassProb (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2) ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v))) = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (t'.image (innerEdgeLE d hNm))) :
-- imply
  (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
-- proof
  apply StatMech.FK.med_wiredMultiHomogeneous_of_cofinal v N t t' hp hp1 htrans

/--
[med_freeMultiHomogeneous_of_cofinal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_freeMultiHomogeneous_of_cofinal_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {v : Site d}
  {N : ℕ}
  {t t' : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (htrans : ∀ᶠ m in atTop, ∀ (hNm : N ≤ m), med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2) ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v))) = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
-- proof
  apply StatMech.FK.med_freeMultiHomogeneous_of_cofinal v N t t' hp hp1 htrans

/--
[med_relift_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_relift_event_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {N₀ N : ℕ}
  {t₀ : Finset (Sym2 (boxVerts d N₀))}
-- given
  (h : N₀ ≤ N) :
-- imply
  cdc_multiOpenEvent ((t₀.image (innerEdgeLE d h)).image (edgeIncl d N)) = cdc_multiOpenEvent (t₀.image (edgeIncl d N₀)) := by
-- proof
  apply StatMech.FK.med_relift_event N₀ N h t₀

/--
[med_wiredMultiHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_wiredMultiHomogeneous_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hplace : med_wiredPlacement hp hp1 g) :
-- imply
  cdc_wiredMultiHomogeneous hp hp1 g := by
-- proof
  apply StatMech.FK.med_wiredMultiHomogeneous hp hp1 g hplace

/--
[med_freeMultiHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_freeMultiHomogeneous_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hplace : med_freePlacement hp hp1 g) :
-- imply
  cdc_freeMultiHomogeneous hp hp1 g := by
-- proof
  apply StatMech.FK.med_freeMultiHomogeneous hp hp1 g hplace

/--
[med_wiredPlacement_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_wiredPlacement_one_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  med_wiredPlacement hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.med_wiredPlacement_one hp hp1

/--
[med_freePlacement_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_freePlacement_one_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  med_freePlacement hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.med_freePlacement_one hp hp1

/--
[med_wiredMultiHomogeneous_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_wiredMultiHomogeneous_one_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  cdc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.med_wiredMultiHomogeneous_one hp hp1

/--
[med_freeMultiHomogeneous_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_freeMultiHomogeneous_one_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  cdc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.med_freeMultiHomogeneous_one hp hp1

/--
[med_wiredIV_isTranslationInvariant_of_placement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_wiredIV_isTranslationInvariant_of_placement_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hplace : ∀ g : Multiplicative (Site d), med_wiredPlacement hp hp1 g) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.med_wiredIV_isTranslationInvariant_of_placement hp hp1 hplace

/--
[med_freeIV_isTranslationInvariant_of_placement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean)
-/
@[path]
private lemma med_freeIV_isTranslationInvariant_of_placement_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hplace : ∀ g : Multiplicative (Site d), med_freePlacement hp hp1 g) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.med_freeIV_isTranslationInvariant_of_placement hp hp1 hplace


-- created on 2026-10-23
