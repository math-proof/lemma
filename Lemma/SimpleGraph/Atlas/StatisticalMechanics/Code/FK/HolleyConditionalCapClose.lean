import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.HolleyConditionalCapClose.Part2
open MeasureTheory Filter Topology Set SimpleGraph StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[hcc_factorise_of_caps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyConditionalCapClose.lean)
-/
@[path]
private lemma hcc_factorise_of_caps_eq
  {d : ℕ}
  {p : ℝ}
  {N r : ℕ}
  {g : Multiplicative (Site d)}
  {T T' : Finset (Sym2 (Site d))}
  {F : Finset (Sym2 (boxVerts d (N + r)))}
  {S_A S_B : Set (ConfigSpace (Sym2 (boxVerts d (N + r))))}
  {C' : SimpleGraph (boxVerts d (N + r))}
  [DecidableRel C'.Adj]
  {tcross : Finset (Sym2 (boxVerts d (N + r)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcross : fmu_multiOpen T ∩ (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T' = boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B))
  (hcrossReal : T ∪ T'.image (fun e => g⁻¹ • e) = tcross.image (edgeIncl d (N + r)))
  (hmeasAB : MeasurableSet (boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B)))
  (hmeasB : MeasurableSet (boxRestrict d (N + r) ⁻¹' S_B))
  (hSAinc : IsIncreasing S_A)
  (hSBout : DependsOnOutside F S_B)
  (hCC' : boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C')
  (hαcap : ∀ ψ ∈ fibreReps F, (∑ ρ, S_A.indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))
  (hBcap : (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d (N + r) ⁻¹' S_B) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) :
-- imply
  ∀ m, N + r ≤ m → (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T ∩ (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := by
-- proof
  apply StatMech.FK.hcc_factorise_of_caps hp hp1 N r g T T' F S_A S_B C' tcross hcross hcrossReal hmeasAB hmeasB hSAinc hSBout hCC' hαcap hBcap

/--
[hcc_wiredDisjointBoxFactorise_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyConditionalCapClose.lean)
-/
@[path]
private lemma hcc_wiredDisjointBoxFactorise_of_data_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdata : hcc_NearBoxFactoriseData (d := d) hp hp1) :
-- imply
  fwm_WiredDisjointBoxFactorise hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FK.hcc_wiredDisjointBoxFactorise_of_data hp hp1 hdata

/--
[hcc_wiredIV_isErgodic_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyConditionalCapClose.lean)
-/
@[path]
private lemma hcc_wiredIV_isErgodic_of_data_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdata : hcc_NearBoxFactoriseData (d := d) hp hp1) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.hcc_wiredIV_isErgodic_of_data hp hp1 hdata

/--
[hcc_nearBoxFactoriseData_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyConditionalCapClose.lean)
-/
@[path]
private lemma hcc_nearBoxFactoriseData_nonvacuous_eq
  {d : ℕ}
  {p : ℝ}
  {N : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∃ (g : Multiplicative (Site d)) (r : ℕ), ∃ (F : Finset (Sym2 (boxVerts d (N + r)))) (S_A S_B : Set (ConfigSpace (Sym2 (boxVerts d (N + r))))) (C' : SimpleGraph (boxVerts d (N + r))) (_ : DecidableRel C'.Adj) (tcross : Finset (Sym2 (boxVerts d (N + r)))), (fmu_multiOpen (∅ : Finset (Sym2 (Site d))) ∩ (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen (∅ : Finset (Sym2 (Site d)))) = boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B) ∧ (∅ : Finset (Sym2 (Site d))) ∪ (∅ : Finset (Sym2 (Site d))).image (fun e => g⁻¹ • e) = tcross.image (edgeIncl d (N + r)) ∧ MeasurableSet (boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B)) ∧ MeasurableSet (boxRestrict d (N + r) ⁻¹' S_B) ∧ IsIncreasing S_A ∧ DependsOnOutside F S_B ∧ boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C' ∧ (∀ ψ ∈ fibreReps F, (∑ ρ, (Set.univ : Set (ConfigSpace (Sym2 (boxVerts d (N + r))))).indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) ∧ ((wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d (N + r) ⁻¹' S_B) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FK.hcc_nearBoxFactoriseData_nonvacuous hp hp1 N


-- created on 2026-10-23
