/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyConditionalCapClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKWiredDomainMonotone.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxReduce.Part2
import Def.StatisticalMechanics.Code.FK.HolleyConditionalCapClose
open MeasureTheory Filter Topology Set SimpleGraph
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


theorem hcc_wiredDisjointBoxFactorise_of_data {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdata : hcc_NearBoxFactoriseData (d := d) hp hp1) :
    fwm_WiredDisjointBoxFactorise hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) := by
  intro P N hreal
  obtain ⟨g, r, hg⟩ := hdata P N hreal
  refine ⟨g, r, fun T hT T' hT' => ?_⟩
  obtain ⟨F, S_A, S_B, C', hC'dec, tcross, hcross, hcrossReal, hmeasAB, hmeasB, hSAinc, hSBout,
    hCC', hαcap, hBcap⟩ := hg T hT T' hT'
  refine ⟨⟨tcross, hcrossReal⟩, ?_⟩
  
  have hfac := hcc_factorise_of_caps hp hp1 N r g T T' F S_A S_B C' tcross hcross hcrossReal
    hmeasAB hmeasB hSAinc hSBout hCC' hαcap hBcap (N + r) (le_refl _)
  exact hfac


theorem hcc_wiredIV_isErgodic_of_data {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdata : hcc_NearBoxFactoriseData (d := d) hp hp1) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fwm_wiredIV_isErgodic_of_factorise hp hp1
    (hcc_wiredDisjointBoxFactorise_of_data hp hp1 hdata)


theorem hcc_nearBoxFactoriseData_nonvacuous {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ) :
    ∃ (g : Multiplicative (Site d)) (r : ℕ),
      ∃ (F : Finset (Sym2 (boxVerts d (N + r))))
        (S_A S_B : Set (ConfigSpace (Sym2 (boxVerts d (N + r)))))
        (C' : SimpleGraph (boxVerts d (N + r))) (_ : DecidableRel C'.Adj)
        (tcross : Finset (Sym2 (boxVerts d (N + r)))),
        (fmu_multiOpen (∅ : Finset (Sym2 (Site d))) ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen (∅ : Finset (Sym2 (Site d))))
            = boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B) ∧
        (∅ : Finset (Sym2 (Site d))) ∪
            (∅ : Finset (Sym2 (Site d))).image (fun e => g⁻¹ • e)
              = tcross.image (edgeIncl d (N + r)) ∧
        MeasurableSet (boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B)) ∧
        MeasurableSet (boxRestrict d (N + r) ⁻¹' S_B) ∧
        IsIncreasing S_A ∧
        DependsOnOutside F S_B ∧
        boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C' ∧
        (∀ ψ ∈ fibreReps F,
          (∑ ρ, (Set.univ : Set (ConfigSpace (Sym2 (boxVerts d (N + r))))).indicator
              (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ)
            ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real
                  (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) ∧
        ((wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d (N + r) ⁻¹' S_B)
          ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real
                (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) := by
  classical
  refine ⟨1, 0, ∅, Set.univ, Set.univ, boundaryCliqueGraph (boxBoundary d (N + 0)),
    inferInstance, ∅, ?_, ?_, ?_, ?_, ?_, ?_, le_refl _, ?_, ?_⟩
  · 
    rw [fmu_multiOpen_empty, Set.preimage_univ, Set.inter_univ, Set.inter_univ, Set.preimage_univ]
  · 
    simp
  · rw [Set.inter_univ, Set.preimage_univ]; exact MeasurableSet.univ
  · rw [Set.preimage_univ]; exact MeasurableSet.univ
  · exact fun _ _ _ ha => ha
  · exact fun _ _ _ => Iff.rfl
  · intro ψ _
    rw [fmu_multiOpen_empty, fdb_wiredMeasure_real_univ]
    have : (∑ ρ, (Set.univ : Set (ConfigSpace (Sym2 (boxVerts d (N + 0))))).indicator
          (fun _ => (1:ℝ)) ρ
          * condBcProb (boxGraph d (N + 0)) (boundaryCliqueGraph (boxBoundary d (N + 0))) p 2 ∅ ψ ρ)
        = ∑ ρ, condBcProb (boxGraph d (N + 0))
            (boundaryCliqueGraph (boxBoundary d (N + 0))) p 2 ∅ ψ ρ := by
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [Set.indicator_of_mem (Set.mem_univ ρ), one_mul]
    rw [this, condBcProb_sum_eq_one (boxGraph d (N + 0))
      (boundaryCliqueGraph (boxBoundary d (N + 0))) hp hp1 (by norm_num) ∅ ψ]
  · rw [Set.preimage_univ, fmu_multiOpen_empty, fdb_wiredMeasure_real_univ,
      fdb_wiredMeasure_real_univ]

end FK
end StatMech
