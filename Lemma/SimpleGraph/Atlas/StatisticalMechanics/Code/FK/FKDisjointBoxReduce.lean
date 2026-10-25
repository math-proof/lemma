import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxReduce.Part2
open MeasureTheory Filter Topology Set SimpleGraph StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fdb_boxMass_eq_bcProb_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxReduce.lean)
-/
@[path]
private lemma fdb_boxMass_eq_bcProb_sum_eq
  {d : ℕ}
  {m : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d m)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S) = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)), S.indicator (fun _ => (1:ℝ)) ω * bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p 2 ω := by
-- proof
  apply StatMech.FK.fdb_boxMass_eq_bcProb_sum m hp hp1 S hmeas

/--
[fdb_finiteBoxDisjointProductDom_of_boxCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxReduce.lean)
-/
@[path]
private lemma fdb_finiteBoxDisjointProductDom_of_boxCap_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcap : fdb_BoxConditionalProductCap (d := d) hp hp1) :
-- imply
  ftb_FiniteBoxDisjointProductDom hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FK.fdb_finiteBoxDisjointProductDom_of_boxCap hp hp1 hcap

/--
[fmu_multiOpen_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxReduce.lean)
-/
@[path]
private lemma fmu_multiOpen_empty_eq
  {d : ℕ} :
-- imply
  fmu_multiOpen (∅ : Finset (Sym2 (Site d))) = Set.univ := by
-- proof
  apply StatMech.FK.fmu_multiOpen_empty

/--
[fdb_wiredMeasure_real_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxReduce.lean)
-/
@[path]
private lemma fdb_wiredMeasure_real_univ_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real Set.univ = 1 := by
-- proof
  apply StatMech.FK.fdb_wiredMeasure_real_univ n hp hp1

/--
[fdb_boxConditionalProductCap_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxReduce.lean)
-/
@[path]
private lemma fdb_boxConditionalProductCap_nonvacuous_eq
  {d : ℕ}
  {p : ℝ}
  {N : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∃ g : Multiplicative (Site d), ∀ᶠ m in atTop, ∃ (F : Finset (Sym2 (boxVerts d m))) (S_A S_B : Set (ConfigSpace (Sym2 (boxVerts d m)))) (C' : SimpleGraph (boxVerts d m)) (_ : DecidableRel C'.Adj), (fmu_multiOpen (∅ : Finset (Sym2 (Site d))) ∩ (shift (1 : Multiplicative (Site d)) : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen (∅ : Finset (Sym2 (Site d)))) = boxRestrict d m ⁻¹' (S_A ∩ S_B) ∧ MeasurableSet (boxRestrict d m ⁻¹' (S_A ∩ S_B)) ∧ MeasurableSet (boxRestrict d m ⁻¹' S_B) ∧ IsIncreasing S_A ∧ DependsOnOutside F S_B ∧ boundaryCliqueGraph (boxBoundary d m) ≤ C' ∧ (0 ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) ∧ (∀ ψ ∈ fibreReps F, (∑ ρ, (Set.univ : Set (ConfigSpace (Sym2 (boxVerts d m)))).indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d m) C' p 2 F ψ ρ) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) ∧ ((wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S_B) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FK.fdb_boxConditionalProductCap_nonvacuous hp hp1 N

/--
[fdb_wiredIV_isErgodic_of_boxCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxReduce.lean)
-/
@[path]
private lemma fdb_wiredIV_isErgodic_of_boxCap_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcap : fdb_BoxConditionalProductCap (d := d) hp hp1) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fdb_wiredIV_isErgodic_of_boxCap hp hp1 hcap


-- created on 2026-10-23
