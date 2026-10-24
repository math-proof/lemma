import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FreeWiredAgreeClose
open MeasureTheory Filter Topology Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fwa_freeIV_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_freeIV_congr_eq
  {d : ℕ}
  {d : ℕ}
  {p₁ p₂ : ℝ}
-- given
  (hp₁ : 0 < p₁)
  (hp1₁ : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp1₂ : p₂ < 1)
  (heq : p₁ = p₂) :
-- imply
  (freeInfiniteVolume d hp₁ hp1₁ (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = (freeInfiniteVolume d hp₂ hp1₂ (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fwa_freeIV_congr d hp₁ hp1₁ hp₂ hp1₂ heq

/--
[fwa_wiredIV_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_wiredIV_congr_eq
  {d : ℕ}
  {d : ℕ}
  {p₁ p₂ : ℝ}
-- given
  (hp₁ : 0 < p₁)
  (hp1₁ : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp1₂ : p₂ < 1)
  (heq : p₁ = p₂) :
-- imply
  (wiredInfiniteVolume d hp₁ hp1₁ (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d hp₂ hp1₂ (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fwa_wiredIV_congr d hp₁ hp1₁ hp₂ hp1₂ heq

/--
[fwa_eventMassProb_free_at_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_eventMassProb_free_at_p_eq
  {d : ℕ}
  {d N : ℕ}
  {p : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  eventMassProb (fuc_freeMass d N (fsc_logit p)) A = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fwa_eventMassProb_free_at_p d N hp hp1 A

/--
[fwa_eventMassProb_wired_at_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_eventMassProb_wired_at_p_eq
  {d : ℕ}
  {d N : ℕ}
  {p : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  eventMassProb (fuc_wiredMass d N (fsc_logit p)) A = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fwa_eventMassProb_wired_at_p d N hp hp1 A

/--
[fwa_edgeIncl_boxVertInclLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_edgeIncl_boxVertInclLE_eq
  {d : ℕ}
  {N m : ℕ}
  {e : Sym2 (boxVerts d N)}
-- given
  (h : N ≤ m) :
-- imply
  edgeIncl d m (Sym2.map (boxVertInclLE d h) e) = edgeIncl d N e := by
-- proof
  apply StatMech.FK.fwa_edgeIncl_boxVertInclLE h e

/--
[fwa_rerealise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_rerealise_eq
  {d : ℕ}
  {N m : ℕ}
  {t₀ : Finset (Sym2 (boxVerts d N))}
-- given
  (h : N ≤ m) :
-- imply
  t₀.image (edgeIncl d N) = (t₀.image (Sym2.map (boxVertInclLE d h))).image (edgeIncl d m) := by
-- proof
  apply StatMech.FK.fwa_rerealise h t₀

/--
[fwa_badTilt_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_badTilt_countable_eq
  {d : ℕ}
  {N : ℕ}
-- given
  (hd : 1 ≤ d)
  (hN : 1 ≤ N) :
-- imply
  (fwa_badTilt d N).Countable := by
-- proof
  apply StatMech.FK.fwa_badTilt_countable hd hN

/--
[fwa_badP_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_badP_countable_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (fwa_badP d).Countable := by
-- proof
  apply StatMech.FK.fwa_badP_countable hd

/--
[fwa_box_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_box_agree_eq
  {d : ℕ}
  {p : ℝ}
  {N : ℕ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hbad : p ∉ fwa_badP d)
  (hN : 1 ≤ N)
  (hA : IsIncreasing A) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fwa_box_agree hd hp hp1 hbad hN hA

/--
[fwa_multiOpen_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_multiOpen_agree_eq
  {d : ℕ}
  {p : ℝ}
  {T : Finset (Sym2 (Site d))}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hbad : p ∉ fwa_badP d) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) := by
-- proof
  apply StatMech.FK.fwa_multiOpen_agree hd hp hp1 hbad T

/--
[fwa_FreeWiredAgree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_FreeWiredAgree_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hbad : p ∉ fwa_badP d) :
-- imply
  fie_FreeWiredAgree (d := d) hp hp1 := by
-- proof
  apply StatMech.FK.fwa_FreeWiredAgree hd hp hp1 hbad

/--
[fwa_freeIV_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_freeIV_isErgodic_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hbad : p ∉ fwa_badP d) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fwa_freeIV_isErgodic hd hp hp1 hbad

/--
[fwa_fk_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_fk_limits_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hbad : p ∉ fwa_badP d) :
-- imply
  (∀ (N : ℕ) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing S → Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))) ∧ (∀ (N : ℕ) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing S → Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))) ∧ IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) ∧ IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) ∧ IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) ∧ IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) ∧ (∀ (N : ℕ) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing S → (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) := by
-- proof
  apply StatMech.FK.fwa_fk_limits hd hp hp1 hbad

/--
[fwa_Ioo_not_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_Ioo_not_countable_eq
  {d : ℕ} :
-- imply
  ¬ (Set.Ioo (0:ℝ) 1).Countable := by
-- proof
  apply StatMech.FK.fwa_Ioo_not_countable

/--
[fwa_exists_good](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean)
-/
@[path]
private lemma fwa_exists_good_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∃ p : ℝ, 0 < p ∧ p < 1 ∧ p ∉ fwa_badP d := by
-- proof
  apply StatMech.FK.fwa_exists_good hd


-- created on 2026-10-23
