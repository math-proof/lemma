import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling
open MeasureTheory Filter Topology Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[ftb_fmu_eq_cdc_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_fmu_eq_cdc_multiOpen_eq
  {d : ℕ}
  {T : Finset (Sym2 (Site d))} :
-- imply
  fmu_multiOpen T = cdc_multiOpenEvent T := by
-- proof
  apply StatMech.FK.ftb_fmu_eq_cdc_multiOpen T

/--
[ftb_boxMass_multiOpen_tendsto_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_boxMass_multiOpen_tendsto_wired_eq
  {d : ℕ}
  {T : Finset (Sym2 (Site d))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))) := by
-- proof
  apply StatMech.FK.ftb_boxMass_multiOpen_tendsto_wired T hp hp1

/--
[ftb_boxMass_multiOpen_tendsto_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_boxMass_multiOpen_tendsto_free_eq
  {d : ℕ}
  {T : Finset (Sym2 (Site d))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))) := by
-- proof
  apply StatMech.FK.ftb_boxMass_multiOpen_tendsto_free T hp hp1

/--
[ftb_boxProd_multiOpen_tendsto_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_boxProd_multiOpen_tendsto_wired_eq
  {d : ℕ}
  {T T' : Finset (Sym2 (Site d))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T'))) := by
-- proof
  apply StatMech.FK.ftb_boxProd_multiOpen_tendsto_wired T T' hp hp1

/--
[ftb_boxProd_multiOpen_tendsto_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_boxProd_multiOpen_tendsto_free_eq
  {d : ℕ}
  {T T' : Finset (Sym2 (Site d))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T'))) := by
-- proof
  apply StatMech.FK.ftb_boxProd_multiOpen_tendsto_free T T' hp hp1

/--
[ftb_iv_le_box_multiOpen_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_iv_le_box_multiOpen_wired_eq
  {d : ℕ}
  {N m : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t.image (edgeIncl d N))) ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t.image (edgeIncl d N))) := by
-- proof
  apply StatMech.FK.ftb_iv_le_box_multiOpen_wired hNm t hp hp1

/--
[ftb_multiOpen_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_multiOpen_inter_eq
  {d : ℕ}
  {s₁ s₂ : Finset (Sym2 (Site d))} :
-- imply
  fmu_multiOpen s₁ ∩ fmu_multiOpen s₂ = fmu_multiOpen (s₁ ∪ s₂) := by
-- proof
  apply StatMech.FK.ftb_multiOpen_inter s₁ s₂

/--
[ftb_cross_eq_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_cross_eq_multiOpen_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {T T' : Finset (Sym2 (Site d))} :
-- imply
  fmu_multiOpen T ∩ (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T' = fmu_multiOpen (T ∪ T'.image (fun e => g⁻¹ • e)) := by
-- proof
  apply StatMech.FK.ftb_cross_eq_multiOpen g T T'

/--
[ftb_iv_le_box_multiOpen_wired_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_iv_le_box_multiOpen_wired_eventually_eq
  {d : ℕ}
  {s : Finset (Sym2 (Site d))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∀ᶠ m in atTop, (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s) ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s) := by
-- proof
  apply StatMech.FK.ftb_iv_le_box_multiOpen_wired_eventually s hp hp1

/--
[ftb_exists_common_box_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_exists_common_box_wired_eq
  {d : ℕ}
  {P : Finset (Finset (Sym2 (Site d)))}
  {p : ℝ}
  {δ : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hδ : 0 < δ) :
-- imply
  ∃ m : ℕ, ∀ T ∈ P, ∀ T' ∈ P, := by
-- proof
  apply StatMech.FK.ftb_exists_common_box_wired P hp hp1 hδ

/--
[ftb_exists_common_box_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_exists_common_box_free_eq
  {d : ℕ}
  {P : Finset (Finset (Sym2 (Site d)))}
  {p : ℝ}
  {δ : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hδ : 0 < δ) :
-- imply
  ∃ m : ℕ, ∀ T ∈ P, ∀ T' ∈ P, := by
-- proof
  apply StatMech.FK.ftb_exists_common_box_free P hp hp1 hδ

/--
[ftb_farBoxProductDom_of_finiteBox_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_farBoxProductDom_of_finiteBox_wired_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hfin : ftb_FiniteBoxDisjointProductDom hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))))) :
-- imply
  ftb_FarBoxProductDom hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ftb_farBoxProductDom_of_finiteBox_wired hp hp1 hfin

/--
[ftb_upperDecay_of_farBoxProductDom_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_upperDecay_of_farBoxProductDom_wired_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdom : ftb_FarBoxProductDom hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  fmu_UpperDecay (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ftb_upperDecay_of_farBoxProductDom_wired hp hp1 hdom

/--
[ftb_upperDecay_of_farBoxProductDom_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_upperDecay_of_farBoxProductDom_free_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdom : ftb_FarBoxProductDom hp hp1 (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  fmu_UpperDecay (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ftb_upperDecay_of_farBoxProductDom_free hp hp1 hdom

/--
[ftb_wiredIV_isErgodic_of_farBoxProductDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_wiredIV_isErgodic_of_farBoxProductDom_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdom : ftb_FarBoxProductDom hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ftb_wiredIV_isErgodic_of_farBoxProductDom hp hp1 hdom

/--
[ftb_wiredIV_isErgodic_of_finiteBoxDisjointProductDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_wiredIV_isErgodic_of_finiteBoxDisjointProductDom_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hfin : ftb_FiniteBoxDisjointProductDom hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ftb_wiredIV_isErgodic_of_finiteBoxDisjointProductDom hp hp1 hfin

/--
[ftb_freeIV_fkg_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_freeIV_fkg_multiOpen_eq
  {d : ℕ}
  {p : ℝ}
  {s₁ s₂ : Finset (Sym2 (Site d))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₁) * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₂) ≤ (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₁ ∩ fmu_multiOpen s₂) := by
-- proof
  apply StatMech.FK.ftb_freeIV_fkg_multiOpen hp hp1 s₁ s₂

/--
[ftb_freeIV_isErgodic_of_farBoxProductDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_freeIV_isErgodic_of_farBoxProductDom_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdom : ftb_FarBoxProductDom hp hp1 (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ftb_freeIV_isErgodic_of_farBoxProductDom hp hp1 hdom

/--
[ftb_farBoxProductDom_dirac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_farBoxProductDom_dirac_eq
  {d : ℕ}
  {p : ℝ}
  [MeasurableSingletonClass (ConfigSpace (Sym2 (Site d)))]
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ftb_FarBoxProductDom hp hp1 (fun _ => (Measure.dirac (fun _ : Sym2 (Site d) => true))) (Measure.dirac (fun _ : Sym2 (Site d) => true)) := by
-- proof
  apply StatMech.FK.ftb_farBoxProductDom_dirac hp hp1

/--
[ftb_finiteBoxDisjointProductDom_dirac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_finiteBoxDisjointProductDom_dirac_eq
  {d : ℕ}
  {p : ℝ}
  [MeasurableSingletonClass (ConfigSpace (Sym2 (Site d)))]
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ftb_FiniteBoxDisjointProductDom hp hp1 (fun _ => (Measure.dirac (fun _ : Sym2 (Site d) => true))) := by
-- proof
  apply StatMech.FK.ftb_finiteBoxDisjointProductDom_dirac hp hp1

/--
[ftb_residue_implies_target_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean)
-/
@[path]
private lemma ftb_residue_implies_target_wired_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdom : ftb_FarBoxProductDom hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  fmu_UpperDecay (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ftb_residue_implies_target_wired hp hp1 hdom


-- created on 2026-10-23
