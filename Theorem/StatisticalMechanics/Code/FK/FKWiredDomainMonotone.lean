/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


theorem fwm_wired_box_domain_monotone (N m : ℕ) (hNm : N ≤ m) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNm
  
  have hanti := fkWiredLimit_antitone N hp hp1 hS
  have h := hanti (Nat.zero_le k)
  simpa using h


theorem fwm_wired_multiOpen_domain_monotone (N m : ℕ) (hNm : N ≤ m)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen (t.image (edgeIncl d N)))
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen (t.image (edgeIncl d N))) := by
  rw [ftb_fmu_eq_cdc_multiOpen, cdc_multiOpenEvent_image_eq_boxRestrict]
  exact fwm_wired_box_domain_monotone N m hNm hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t)


theorem fwm_wired_domain_monotone_of_realised {N m : ℕ} (hNm : N ≤ m)
    {s : Finset (Sym2 (Site d))} (t : Finset (Sym2 (boxVerts d N)))
    (hst : s = t.image (edgeIncl d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s)
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s) := by
  subst hst
  exact fwm_wired_multiOpen_domain_monotone N m hNm t hp hp1


theorem fwm_wired_cross_le_box_domain {N m : ℕ} (hNm : N ≤ m)
    (g : Multiplicative (Site d)) (T T' : Finset (Sym2 (Site d)))
    {t : Finset (Sym2 (boxVerts d N))}
    (hreal : T ∪ T'.image (fun e => g⁻¹ • e) = t.image (edgeIncl d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T') := by
  rw [ftb_cross_eq_multiOpen g T T']
  exact fwm_wired_domain_monotone_of_realised hNm t hreal hp hp1


end FK
end StatMech
