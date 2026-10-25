/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyConditionalCapClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKWiredDomainMonotone.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxReduce.Part2
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


theorem hcc_factorise_of_caps {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (N r : ℕ) (g : Multiplicative (Site d)) (T T' : Finset (Sym2 (Site d)))
    (F : Finset (Sym2 (boxVerts d (N + r))))
    (S_A S_B : Set (ConfigSpace (Sym2 (boxVerts d (N + r)))))
    (C' : SimpleGraph (boxVerts d (N + r))) [DecidableRel C'.Adj]
    (tcross : Finset (Sym2 (boxVerts d (N + r))))
    (hcross : fmu_multiOpen T ∩
        (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
          ⁻¹' fmu_multiOpen T' = boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B))
    (hcrossReal : T ∪ T'.image (fun e => g⁻¹ • e) = tcross.image (edgeIncl d (N + r)))
    (hmeasAB : MeasurableSet (boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B)))
    (hmeasB : MeasurableSet (boxRestrict d (N + r) ⁻¹' S_B))
    (hSAinc : IsIncreasing S_A) (hSBout : DependsOnOutside F S_B)
    (hCC' : boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C')
    (hαcap : ∀ ψ ∈ fibreReps F,
      (∑ ρ, S_A.indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ)
        ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))
    (hBcap : (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d (N + r) ⁻¹' S_B)
        ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) :
    ∀ m, N + r ≤ m →
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T')
        ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := by
  intro m hm
  set α := (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) with hαdef
  have hαnn : 0 ≤ α := by rw [hαdef]; exact measureReal_nonneg
  
  have hbridge :
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T')
        ≤ (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (fmu_multiOpen T ∩
                (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                  ⁻¹' fmu_multiOpen T') :=
    fwm_wired_cross_le_box_domain hm g T T' hcrossReal hp hp1
  
  have hcrossmass :
      (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T')
        = ∑ ω : ConfigSpace (Sym2 (boxVerts d (N + r))),
            (S_A ∩ S_B).indicator (fun _ => (1:ℝ)) ω
              * bcProb (boxGraph d (N + r)) (boundaryCliqueGraph (boxBoundary d (N + r))) p 2 ω := by
    rw [hcross, fdb_boxMass_eq_bcProb_sum (N + r) hp hp1 (S_A ∩ S_B) hmeasAB]
  
  have hBmass :
      (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d (N + r) ⁻¹' S_B)
        = ∑ ω : ConfigSpace (Sym2 (boxVerts d (N + r))),
            S_B.indicator (fun _ => (1:ℝ)) ω
              * bcProb (boxGraph d (N + r)) (boundaryCliqueGraph (boxBoundary d (N + r))) p 2 ω :=
    fdb_boxMass_eq_bcProb_sum (N + r) hp hp1 S_B hmeasB
  
  have hdecouple :
      (∑ ω : ConfigSpace (Sym2 (boxVerts d (N + r))),
          (S_A ∩ S_B).indicator (fun _ => (1:ℝ)) ω
            * bcProb (boxGraph d (N + r)) (boundaryCliqueGraph (boxBoundary d (N + r))) p 2 ω)
        ≤ α * (∑ ω : ConfigSpace (Sym2 (boxVerts d (N + r))),
            S_B.indicator (fun _ => (1:ℝ)) ω
              * bcProb (boxGraph d (N + r)) (boundaryCliqueGraph (boxBoundary d (N + r))) p 2 ω) :=
    bcProb_disjoint_product_dom_wired (boxGraph d (N + r))
      (boundaryCliqueGraph (boxBoundary d (N + r))) hp hp1 (by norm_num : (1:ℝ) ≤ 2)
      C' hCC' hSAinc hSBout hαnn hαcap
  
  calc (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T')
      ≤ (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T') := hbridge
    _ = ∑ ω : ConfigSpace (Sym2 (boxVerts d (N + r))),
            (S_A ∩ S_B).indicator (fun _ => (1:ℝ)) ω
              * bcProb (boxGraph d (N + r))
                  (boundaryCliqueGraph (boxBoundary d (N + r))) p 2 ω := hcrossmass
    _ ≤ α * (∑ ω : ConfigSpace (Sym2 (boxVerts d (N + r))),
            S_B.indicator (fun _ => (1:ℝ)) ω
              * bcProb (boxGraph d (N + r))
                  (boundaryCliqueGraph (boxBoundary d (N + r))) p 2 ω) := hdecouple
    _ = α * (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d (N + r) ⁻¹' S_B) := by
          rw [hBmass]
    _ ≤ α * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') :=
          mul_le_mul_of_nonneg_left hBcap hαnn


end FK
end StatMech
