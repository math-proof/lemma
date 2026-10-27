import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
open MeasureTheory Filter Topology SimpleGraph Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fkgqt_centred_eq_translated_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_centred_eq_translated_wired_eq
  {d : ℕ}
  {m : ℕ}
  {v : Site d}
  {t : Finset (Sym2 (boxVerts d m))}
  {p q : ℝ} :
-- imply
  med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) t = med_multiMassProb (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p q) (t.image (Sym2.map (fvs_transEquiv d m v))) := by
-- proof
  apply StatMech.FK.fkgqt_centred_eq_translated_wired m v t p q

/--
[fkgqt_centred_med_eq_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_centred_med_eq_measure_eq
  {d : ℕ}
  {n : ℕ}
  {tb : Finset (Sym2 (boxVerts d n))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  med_multiMassProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p q) tb = (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (tb.image (edgeIncl d n))) := by
-- proof
  apply StatMech.FK.fkgqt_centred_med_eq_measure n tb hp hp1 hq

/--
[fkgqt_transBoxMass_eq_centred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_transBoxMass_eq_centred_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p q : ℝ}
  {m : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hNm : N ≤ m) :
-- imply
  fkgqt_transBoxMass v N t p q m hNm = (wiredFiniteMeasure d m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
-- proof
  apply StatMech.FK.fkgqt_transBoxMass_eq_centred v N t hp hp1 hq m hNm

/--
[fkgqt_transBoxMass_tendsto_centred_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_transBoxMass_tendsto_centred_iv_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun k : ℕ ↦ fkgqt_transBoxMass v N t p q (N + k) (Nat.le_add_right N k)) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
-- proof
  apply StatMech.FK.fkgqt_transBoxMass_tendsto_centred_iv v N t hp hp1 hq

/--
[fkgqt_squeeze_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_squeeze_lower_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p q : ℝ}
  {m : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hNm : N ≤ m)
  (hm : 1 ≤ m) :
-- imply
  (wiredFiniteMeasure d (m + flc_vrad v + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e ↦ (Multiplicative.ofAdd v) • e))) ≤ fkgqt_transBoxMass v N t p q m hNm := by
-- proof
  apply StatMech.FK.fkgqt_squeeze_lower v N t hp hp1 hq m hNm hm

/--
[fkgqt_squeeze_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_squeeze_upper_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p q : ℝ}
  {m a : ℕ}
  {tb : Finset (Sym2 (boxVerts d a))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hNm : N ≤ m)
  (ha : 1 ≤ a)
  (hcond : a + flc_vrad v + 1 ≤ m)
  (htb : tb.image (edgeIncl d a) = (t.image (edgeIncl d N)).image (fun e ↦ (Multiplicative.ofAdd v) • e)) :
-- imply
  fkgqt_transBoxMass v N t p q m hNm ≤ (wiredFiniteMeasure d a hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e ↦ (Multiplicative.ofAdd v) • e))) := by
-- proof
  apply StatMech.FK.fkgqt_squeeze_upper v N t hp hp1 hq m a hNm ha hcond tb htb

/--
[fkgqt_transBoxMass_tendsto_translated_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_transBoxMass_tendsto_translated_iv_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun k : ℕ ↦ fkgqt_transBoxMass v N t p q (N + k) (Nat.le_add_right N k)) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e ↦ (Multiplicative.ofAdd v) • e))))) := by
-- proof
  apply StatMech.FK.fkgqt_transBoxMass_tendsto_translated_iv v N t hp hp1 hq

/--
[fkgqt_wired_multiOpen_translation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_wired_multiOpen_translation_eq
  {d : ℕ}
  {v : Site d}
  {s : Finset (Sym2 (Site d))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) (cdc_multiOpenEvent s) = (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) (cdc_multiOpenEvent (s.image (fun e ↦ (Multiplicative.ofAdd v) • e))) := by
-- proof
  apply StatMech.FK.fkgqt_wired_multiOpen_translation v s hp hp1 hq

/--
[fkgqt_measure_eq_of_multiOpen_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_measure_eq_of_multiOpen_eq_eq
  {d : ℕ}
  [Countable E]
  {μ ν : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν]
-- given
  (hmom : ∀ T : Finset E, μ (fmu_multiOpen T) = ν (fmu_multiOpen T)) :
-- imply
  μ = ν := by
-- proof
  apply StatMech.FK.fkgqt_measure_eq_of_multiOpen_eq μ ν hmom

/--
[fkgqt_wiredIV_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_wiredIV_isTranslationInvariant_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fkgqt_wiredIV_isTranslationInvariant hp hp1 hq

/--
[fkgqt_centred_eq_translated_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_centred_eq_translated_free_eq
  {d : ℕ}
  {m : ℕ}
  {v : Site d}
  {t : Finset (Sym2 (boxVerts d m))}
  {p q : ℝ} :
-- imply
  med_multiMassProb (fkProb (boxGraph d m) p q) t = med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p q) (t.image (Sym2.map (fvs_transEquiv d m v))) := by
-- proof
  apply StatMech.FK.fkgqt_centred_eq_translated_free m v t p q

/--
[fkgqt_centred_med_eq_measure_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_centred_med_eq_measure_free_eq
  {d : ℕ}
  {n : ℕ}
  {tb : Finset (Sym2 (boxVerts d n))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  med_multiMassProb (fkProb (boxGraph d n) p q) tb = (freeFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (tb.image (edgeIncl d n))) := by
-- proof
  apply StatMech.FK.fkgqt_centred_med_eq_measure_free n tb hp hp1 hq

/--
[fkgqt_transBoxMassFree_eq_centred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_transBoxMassFree_eq_centred_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p q : ℝ}
  {m : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hNm : N ≤ m) :
-- imply
  fkgqt_transBoxMassFree v N t p q m hNm = (freeFiniteMeasure d m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
-- proof
  apply StatMech.FK.fkgqt_transBoxMassFree_eq_centred v N t hp hp1 hq m hNm

/--
[fkgqt_transBoxMassFree_tendsto_centred_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_transBoxMassFree_tendsto_centred_iv_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun k : ℕ ↦ fkgqt_transBoxMassFree v N t p q (N + k) (Nat.le_add_right N k)) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
-- proof
  apply StatMech.FK.fkgqt_transBoxMassFree_tendsto_centred_iv v N t hp hp1 hq

/--
[fkgqt_freeSqueeze_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_freeSqueeze_upper_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p q : ℝ}
  {m : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hNm : N ≤ m) :
-- imply
  fkgqt_transBoxMassFree v N t p q m hNm ≤ (freeFiniteMeasure d (m + flc_vrad v + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e ↦ (Multiplicative.ofAdd v) • e))) := by
-- proof
  apply StatMech.FK.fkgqt_freeSqueeze_upper v N t hp hp1 hq m hNm

/--
[fkgqt_freeSqueeze_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_freeSqueeze_lower_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p q : ℝ}
  {m a : ℕ}
  {tb : Finset (Sym2 (boxVerts d a))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hNm : N ≤ m)
  (hcond : a + flc_vrad v + 1 ≤ m)
  (htb : tb.image (edgeIncl d a) = (t.image (edgeIncl d N)).image (fun e ↦ (Multiplicative.ofAdd v) • e)) :
-- imply
  (freeFiniteMeasure d a hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e ↦ (Multiplicative.ofAdd v) • e))) ≤ fkgqt_transBoxMassFree v N t p q m hNm := by
-- proof
  apply StatMech.FK.fkgqt_freeSqueeze_lower v N t hp hp1 hq m a hNm hcond tb htb

/--
[fkgqt_transBoxMassFree_tendsto_translated_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_transBoxMassFree_tendsto_translated_iv_eq
  {d : ℕ}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun k : ℕ ↦ fkgqt_transBoxMassFree v N t p q (N + k) (Nat.le_add_right N k)) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e ↦ (Multiplicative.ofAdd v) • e))))) := by
-- proof
  apply StatMech.FK.fkgqt_transBoxMassFree_tendsto_translated_iv v N t hp hp1 hq

/--
[fkgqt_free_multiOpen_translation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_free_multiOpen_translation_eq
  {d : ℕ}
  {v : Site d}
  {s : Finset (Sym2 (Site d))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) (cdc_multiOpenEvent s) = (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) (cdc_multiOpenEvent (s.image (fun e ↦ (Multiplicative.ofAdd v) • e))) := by
-- proof
  apply StatMech.FK.fkgqt_free_multiOpen_translation v s hp hp1 hq

/--
[fkgqt_freeIV_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean)
-/
@[path]
private lemma fkgqt_freeIV_isTranslationInvariant_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fkgqt_freeIV_isTranslationInvariant hp hp1 hq


-- created on 2026-10-23
