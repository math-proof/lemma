/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part2
open MeasureTheory
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


lemma measurableSet_connected_removeSite (x a b : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | Connected d (removeSite x ω) a b} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | Connected d (removeSite x ω) a b}
      = (fun ω => removeSite x ω) ⁻¹' {ω' | Connected d ω' a b} := rfl
  rw [h]
  exact (measurable_removeSite x) (measurableSet_connected a b)


theorem measurableSet_isTrifurcation (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | IsTrifurcation d ω x} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | IsTrifurcation d ω x}
      = ⋃ a₁ : Site d, ⋃ a₂ : Site d, ⋃ a₃ : Site d,
          ((if a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ then Set.univ else ∅)
            ∩ ({ω | Connected d ω x a₁} ∩ {ω | Connected d ω x a₂} ∩ {ω | Connected d ω x a₃})
            ∩ ({ω | (cluster d ω a₁).Infinite} ∩ {ω | (cluster d ω a₂).Infinite}
                ∩ {ω | (cluster d ω a₃).Infinite})
            ∩ ({ω | ¬ Connected d (removeSite x ω) a₁ a₂}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₁ a₃}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₂ a₃})) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨a₁, a₂, a₃, hne, hconn, hinf, hsep⟩
      refine ⟨a₁, a₂, a₃, ⟨⟨⟨?_, ⟨⟨hconn.1, hconn.2.1⟩, hconn.2.2⟩⟩,
        ⟨⟨hinf.1, hinf.2.1⟩, hinf.2.2⟩⟩, ⟨⟨hsep.1, hsep.2.1⟩, hsep.2.2⟩⟩⟩
      rw [if_pos hne]; exact Set.mem_univ _
    · rintro ⟨a₁, a₂, a₃, ⟨⟨⟨hif, ⟨⟨hc1, hc2⟩, hc3⟩⟩, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩⟩
      by_cases hh : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃
      · exact ⟨a₁, a₂, a₃, hh, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
      · rw [if_neg hh] at hif; exact absurd hif (Set.notMem_empty _)
  rw [heq]
  refine MeasurableSet.iUnion fun a₁ => MeasurableSet.iUnion fun a₂ =>
    MeasurableSet.iUnion fun a₃ => ?_
  apply MeasurableSet.inter
  apply MeasurableSet.inter
  apply MeasurableSet.inter
  · by_cases hh : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃
    · rw [if_pos hh]; exact MeasurableSet.univ
    · rw [if_neg hh]; exact MeasurableSet.empty
  · exact ((measurableSet_connected x a₁).inter (measurableSet_connected x a₂)).inter
      (measurableSet_connected x a₃)
  · exact ((measurableSet_clusterInfinite a₁).inter (measurableSet_clusterInfinite a₂)).inter
      (measurableSet_clusterInfinite a₃)
  · exact (((measurableSet_connected_removeSite x a₁ a₂).compl).inter
      ((measurableSet_connected_removeSite x a₁ a₃).compl)).inter
      ((measurableSet_connected_removeSite x a₂ a₃).compl)


theorem isTrifurcation_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    IsTrifurcation d (shift g ω) (g • x) ↔ IsTrifurcation d ω x := by
  constructor
  · rintro ⟨a₁, a₂, a₃, hne, hconn, hinf, hsep⟩
    refine ⟨g⁻¹ • a₁, g⁻¹ • a₂, g⁻¹ • a₃, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun h => hne.1 ?_, fun h => hne.2.1 ?_, fun h => hne.2.2 ?_⟩ <;>
        · apply smul_injective g; simpa [smul_inv_smul] using h
    · refine ⟨?_, ?_, ?_⟩
      · exact (connected_shift g ω x (g⁻¹ • a₁)).mp (by rw [smul_inv_smul]; exact hconn.1)
      · exact (connected_shift g ω x (g⁻¹ • a₂)).mp (by rw [smul_inv_smul]; exact hconn.2.1)
      · exact (connected_shift g ω x (g⁻¹ • a₃)).mp (by rw [smul_inv_smul]; exact hconn.2.2)
    · refine ⟨?_, ?_, ?_⟩
      · have hc := cluster_shift g ω (g⁻¹ • a₁)
        rw [smul_inv_smul] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.1
      · have hc := cluster_shift g ω (g⁻¹ • a₂)
        rw [smul_inv_smul] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.2.1
      · have hc := cluster_shift g ω (g⁻¹ • a₃)
        rw [smul_inv_smul] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.2.2
    · refine ⟨?_, ?_, ?_⟩
      · intro hcon
        apply hsep.1
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₁)) (g • (g⁻¹ • a₂)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₁) (g⁻¹ • a₂)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this
        exact this
      · intro hcon
        apply hsep.2.1
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₁)) (g • (g⁻¹ • a₃)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₁) (g⁻¹ • a₃)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this
        exact this
      · intro hcon
        apply hsep.2.2
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₂)) (g • (g⁻¹ • a₃)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₂) (g⁻¹ • a₃)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this
        exact this
  · rintro ⟨a₁, a₂, a₃, hne, hconn, hinf, hsep⟩
    refine ⟨g • a₁, g • a₂, g • a₃, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun h => hne.1 (smul_injective g h), fun h => hne.2.1 (smul_injective g h),
        fun h => hne.2.2 (smul_injective g h)⟩
    · exact ⟨(connected_shift g ω x a₁).mpr hconn.1,
        (connected_shift g ω x a₂).mpr hconn.2.1,
        (connected_shift g ω x a₃).mpr hconn.2.2⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [cluster_shift g ω a₁]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.1
      · rw [cluster_shift g ω a₂]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.2.1
      · rw [cluster_shift g ω a₃]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.2.2
    · rw [removeSite_shift]
      exact ⟨fun hcon => hsep.1 ((connected_shift g (removeSite x ω) a₁ a₂).mp hcon),
        fun hcon => hsep.2.1 ((connected_shift g (removeSite x ω) a₁ a₃).mp hcon),
        fun hcon => hsep.2.2 ((connected_shift g (removeSite x ω) a₂ a₃).mp hcon)⟩


theorem trifurcationProb_const (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (x : Site d) :
    μ {ω | IsTrifurcation d ω x} = μ {ω | IsTrifurcation d ω 0} := by
  
  set g : Multiplicative (Site d) := Multiplicative.ofAdd x with hg
  have hgx : g • (0 : Site d) = x := by
    show Multiplicative.toAdd g + (0 : Site d) = x
    simp [hg]
  have hpre : (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹'
      {ω | IsTrifurcation d ω x} = {ω | IsTrifurcation d ω 0} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hgx, isTrifurcation_shift g ω 0]
  calc μ {ω | IsTrifurcation d ω x}
      = μ ((shift g) ⁻¹' {ω | IsTrifurcation d ω x}) :=
        (hinv.measure_preimage g (measurableSet_isTrifurcation x)).symm
    _ = μ {ω | IsTrifurcation d ω 0} := by rw [hpre]


end Percolation
end StatMech
