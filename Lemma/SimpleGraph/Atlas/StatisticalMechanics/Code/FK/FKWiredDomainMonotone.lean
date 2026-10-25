import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FKWiredDomainMonotone.Part2
open MeasureTheory Filter Topology Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fwm_wired_box_domain_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_wired_box_domain_monotone_eq
  {d : ℕ}
  {N m : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fwm_wired_box_domain_monotone N m hNm hp hp1 hS

/--
[fwm_wired_multiOpen_domain_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_wired_multiOpen_domain_monotone_eq
  {d : ℕ}
  {N m : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t.image (edgeIncl d N))) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t.image (edgeIncl d N))) := by
-- proof
  apply StatMech.FK.fwm_wired_multiOpen_domain_monotone N m hNm t hp hp1

/--
[fwm_wired_domain_monotone_of_realised](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_wired_domain_monotone_of_realised_eq
  {d : ℕ}
  {N m : ℕ}
  {s : Finset (Sym2 (Site d))}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hNm : N ≤ m)
  (hst : s = t.image (edgeIncl d N))
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s) := by
-- proof
  apply StatMech.FK.fwm_wired_domain_monotone_of_realised hNm t hst hp hp1

/--
[fwm_wired_cross_le_box_domain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_wired_cross_le_box_domain_eq
  {d : ℕ}
  {N m : ℕ}
  {g : Multiplicative (Site d)}
  {T T' : Finset (Sym2 (Site d))}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hNm : N ≤ m)
  (hreal : T ∪ T'.image (fun e => g⁻¹ • e) = t.image (edgeIncl d N))
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T ∩ (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T ∩ (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') := by
-- proof
  apply StatMech.FK.fwm_wired_cross_le_box_domain hNm g T T' hreal hp hp1

/--
[fwm_finiteBoxDisjointProductDom_conclusion_of_factorise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_finiteBoxDisjointProductDom_conclusion_of_factorise_eq
  {d : ℕ}
  {p : ℝ}
  {P : Finset (Finset (Sym2 (Site d)))}
  {N : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hfac : fwm_WiredDisjointBoxFactorise hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))))
  (hreal : ∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d N)), T = t.image (edgeIncl d N)) :
-- imply
  ∃ g : Multiplicative (Site d), ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P, (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T ∩ (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := by
-- proof
  apply StatMech.FK.fwm_finiteBoxDisjointProductDom_conclusion_of_factorise hp hp1 hfac P N hreal

/--
[fwm_realised_box_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_realised_box_mono_eq
  {d : ℕ}
  {N₀ N : ℕ}
  {s : Finset (Sym2 (Site d))}
  {t : Finset (Sym2 (boxVerts d N₀))}
-- given
  (h : N₀ ≤ N)
  (hst : s = t.image (edgeIncl d N₀)) :
-- imply
  s = (t.image (innerEdgeLE d h)).image (edgeIncl d N) := by
-- proof
  apply StatMech.FK.fwm_realised_box_mono h hst

/--
[fwm_exists_realising_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_exists_realising_box_eq
  {d : ℕ}
  {P : Finset (Finset (Sym2 (Site d)))} :
-- imply
  ∃ N : ℕ, ∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d N)), T = t.image (edgeIncl d N) := by
-- proof
  apply StatMech.FK.fwm_exists_realising_box P

/--
[fwm_exists_common_box_ge_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_exists_common_box_ge_wired_eq
  {d : ℕ}
  {P : Finset (Finset (Sym2 (Site d)))}
  {N₀ : ℕ}
  {p : ℝ}
  {δ : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hδ : 0 < δ) :
-- imply
  ∃ m : ℕ, N₀ ≤ m ∧ ∀ T ∈ P, ∀ T' ∈ P, := by
-- proof
  apply StatMech.FK.fwm_exists_common_box_ge_wired P N₀ hp hp1 hδ

/--
[fwm_upperDecay_of_factorise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_upperDecay_of_factorise_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hfac : fwm_WiredDisjointBoxFactorise hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))))) :
-- imply
  fmu_UpperDecay (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fwm_upperDecay_of_factorise hp hp1 hfac

/--
[fwm_wiredIV_isErgodic_of_factorise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_wiredIV_isErgodic_of_factorise_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hfac : fwm_WiredDisjointBoxFactorise hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fwm_wiredIV_isErgodic_of_factorise hp hp1 hfac

/--
[fwm_wiredDisjointBoxFactorise_dirac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_wiredDisjointBoxFactorise_dirac_eq
  {d : ℕ}
  {p : ℝ}
  [MeasurableSingletonClass (ConfigSpace (Sym2 (Site d)))]
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  fwm_WiredDisjointBoxFactorise hp hp1 (fun _ => (Measure.dirac (fun _ : Sym2 (Site d) => true))) := by
-- proof
  apply StatMech.FK.fwm_wiredDisjointBoxFactorise_dirac hp hp1

/--
[fwm_residue_implies_target_conclusion_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean)
-/
@[path]
private lemma fwm_residue_implies_target_conclusion_wired_eq
  {d : ℕ}
  {p : ℝ}
  {P : Finset (Finset (Sym2 (Site d)))}
  {N : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hfac : fwm_WiredDisjointBoxFactorise hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))))
  (hreal : ∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d N)), T = t.image (edgeIncl d N)) :
-- imply
  ∃ g : Multiplicative (Site d), ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P, (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T ∩ (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := by
-- proof
  apply StatMech.FK.fwm_residue_implies_target_conclusion_wired hp hp1 hfac P N hreal


-- created on 2026-10-23
