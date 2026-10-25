/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.MonotoneVolumeLimit
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


theorem ftb_fmu_eq_cdc_multiOpen (T : Finset (Sym2 (Site d))) :
    fmu_multiOpen T = cdc_multiOpenEvent T := rfl


theorem ftb_boxMass_multiOpen_tendsto_wired (T : Finset (Sym2 (Site d)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))) := by
  obtain ⟨N, t, hTt⟩ := cdc_finset_in_box T
  rw [ftb_fmu_eq_cdc_multiOpen, hTt]
  exact cdc_wired_multiOpenEvent_tendsto N t hp hp1


theorem ftb_boxMass_multiOpen_tendsto_free (T : Finset (Sym2 (Site d)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))) := by
  obtain ⟨N, t, hTt⟩ := cdc_finset_in_box T
  rw [ftb_fmu_eq_cdc_multiOpen, hTt]
  exact cdc_free_multiOpenEvent_tendsto N t hp hp1


theorem ftb_boxProd_multiOpen_tendsto_wired (T T' : Finset (Sym2 (Site d)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T'))) :=
  (ftb_boxMass_multiOpen_tendsto_wired T hp hp1).mul (ftb_boxMass_multiOpen_tendsto_wired T' hp hp1)


theorem ftb_boxProd_multiOpen_tendsto_free (T T' : Finset (Sym2 (Site d)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T'))) :=
  (ftb_boxMass_multiOpen_tendsto_free T hp hp1).mul (ftb_boxMass_multiOpen_tendsto_free T' hp hp1)


theorem ftb_iv_le_box_multiOpen_wired {N m : ℕ} (hNm : N ≤ m)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen (t.image (edgeIncl d N)))
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen (t.image (edgeIncl d N))) := by
  rw [ftb_fmu_eq_cdc_multiOpen, cdc_multiOpenEvent_image_eq_boxRestrict,
    fkWiredLimit_wiredInfiniteVolume_eq N hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t)]
  exact fk_wired_limit_le N m hNm hp hp1 (cdc_boxMultiOpenEvent N t)


theorem ftb_multiOpen_inter (s₁ s₂ : Finset (Sym2 (Site d))) :
    fmu_multiOpen s₁ ∩ fmu_multiOpen s₂ = fmu_multiOpen (s₁ ∪ s₂) := by
  ext ω
  simp only [fmu_multiOpen, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_union]
  constructor
  · rintro ⟨h1, h2⟩ e (he | he)
    · exact h1 e he
    · exact h2 e he
  · intro h; exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩


theorem ftb_cross_eq_multiOpen (g : Multiplicative (Site d)) (T T' : Finset (Sym2 (Site d))) :
    fmu_multiOpen T ∩
        (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
          ⁻¹' fmu_multiOpen T'
      = fmu_multiOpen (T ∪ T'.image (fun e => g⁻¹ • e)) := by
  rw [fmu_shift_multiOpen g T', ftb_multiOpen_inter]


theorem ftb_iv_le_box_multiOpen_wired_eventually (s : Finset (Sym2 (Site d)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∀ᶠ m in atTop,
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s)
        ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s) := by
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  rw [Filter.eventually_atTop]
  refine ⟨N, fun m hm => ?_⟩
  rw [hst]
  exact ftb_iv_le_box_multiOpen_wired hm t hp hp1


theorem ftb_exists_common_box_wired (P : Finset (Finset (Sym2 (Site d))))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, ∀ T ∈ P, ∀ T' ∈ P,
      |(wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
  classical
  
  have hev : ∀ T ∈ P, ∀ T' ∈ P, ∀ᶠ m in atTop,
      |(wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
    intro T _ T' _
    have htend := ftb_boxProd_multiOpen_tendsto_wired T T' hp hp1
    have := htend.eventually (Metric.ball_mem_nhds _ hδ)
    refine this.mono fun n hn => ?_
    rw [Real.dist_eq] at hn
    exact hn
  
  have hbig : ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P,
      |(wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
    rw [Filter.eventually_all_finset P]
    intro T hT
    rw [Filter.eventually_all_finset P]
    intro T' hT'
    exact hev T hT T' hT'
  exact hbig.exists


theorem ftb_exists_common_box_free (P : Finset (Finset (Sym2 (Site d))))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, ∀ T ∈ P, ∀ T' ∈ P,
      |(freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
  classical
  have hev : ∀ T ∈ P, ∀ T' ∈ P, ∀ᶠ m in atTop,
      |(freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
    intro T _ T' _
    have htend := ftb_boxProd_multiOpen_tendsto_free T T' hp hp1
    have := htend.eventually (Metric.ball_mem_nhds _ hδ)
    refine this.mono fun n hn => ?_
    rw [Real.dist_eq] at hn
    exact hn
  have hbig : ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P,
      |(freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
    rw [Filter.eventually_all_finset P]
    intro T hT
    rw [Filter.eventually_all_finset P]
    intro T' hT'
    exact hev T hT T' hT'
  exact hbig.exists


end FK
end StatMech
