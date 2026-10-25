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
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
open MeasureTheory
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


lemma Tcount_eq_sum_indicator (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (Tcount d ω n : ℝ≥0∞) =
      ∑ x ∈ boxFinsetBK d n,
        ({ω' | IsTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
  classical
  unfold Tcount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : IsTrifurcation d ω x
  · rw [if_pos h]
    rw [Set.indicator_of_mem (show ω ∈ {ω' | IsTrifurcation d ω' x} from h)]
  · rw [if_neg h]
    rw [Set.indicator_of_notMem (show ω ∉ {ω' | IsTrifurcation d ω' x} from h)]


theorem expected_Tcount (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (n : ℕ) :
    ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ
      = (boxFinsetBK d n).card • μ {ω | IsTrifurcation d ω 0} := by
  classical
  have hmeas : ∀ x : Site d, Measurable
      (fun ω => ({ω' | IsTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω) :=
    fun x => Measurable.indicator measurable_const (measurableSet_isTrifurcation x)
  calc ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ∑ x ∈ boxFinsetBK d n,
          ({ω' | IsTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        apply lintegral_congr; intro ω; exact Tcount_eq_sum_indicator ω n
    _ = ∑ x ∈ boxFinsetBK d n,
          ∫⁻ ω, ({ω' | IsTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        rw [MeasureTheory.lintegral_finsetSum]
        intro x _; exact hmeas x
    _ = ∑ x ∈ boxFinsetBK d n, μ {ω | IsTrifurcation d ω x} := by
        apply Finset.sum_congr rfl; intro x _
        rw [MeasureTheory.lintegral_indicator (measurableSet_isTrifurcation x)]; simp
    _ = ∑ _x ∈ boxFinsetBK d n, μ {ω | IsTrifurcation d ω 0} := by
        apply Finset.sum_congr rfl; intro x _; exact trifurcationProb_const μ hinv x
    _ = (boxFinsetBK d n).card • μ {ω | IsTrifurcation d ω 0} := by
        rw [Finset.sum_const]


theorem trifurcation_prob_eq_zero (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0)) :
    μ {ω | IsTrifurcation d ω 0} = 0 := by
  classical
  set p : ℝ≥0∞ := μ {ω | IsTrifurcation d ω 0} with hp
  
  have hkey : ∀ n, ((boxFinsetBK d n).card : ℝ≥0∞) * p ≤ (bdry n : ℝ≥0∞) := by
    intro n
    have hexp := expected_Tcount μ hinv n
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ ≤ (bdry n : ℝ≥0∞) := by
      calc ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ
          ≤ ∫⁻ _ω, (bdry n : ℝ≥0∞) ∂μ := by
            apply lintegral_mono; intro ω
            simp only
            exact_mod_cast hbound ω n
        _ = (bdry n : ℝ≥0∞) := by rw [lintegral_const]; simp
    rwa [hexp] at hle
  
  have hpfin : p ≠ ⊤ := by
    rw [hp]; exact (measure_ne_top μ _)
  
  set pr : ℝ := p.toReal with hpr
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  
  have hkeyr : ∀ n, ((boxFinsetBK d n).card : ℝ) * pr ≤ (bdry n : ℝ) := by
    intro n
    have h := hkey n
    have h' : (((boxFinsetBK d n).card : ℝ≥0∞) * p).toReal ≤ (bdry n : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, hpr] using h'
  
  have hvolr : ∀ n, (0 : ℝ) < ((boxFinsetBK d n).card : ℝ) := by
    intro n; exact_mod_cast hvol n
  have hle : ∀ n, pr ≤ (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ) := by
    intro n
    rw [le_div_iff₀ (hvolr n)]
    linarith [hkeyr n]
  have hpr0 : pr ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hdens hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this


theorem numInfiniteClusters_ae_const_uniqueness
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ) :
    ∃ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 :=
  numInfiniteClusters_ae_const μ herg


theorem numInfiniteClusters_ae_const_ne_top
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    
    
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0}) :
    ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
  
  have htri0 : μ {ω | IsTrifurcation d ω 0} = 0 :=
    trifurcation_prob_eq_zero μ herg.isTranslationInvariant bdry hbound hvol hdens
  
  have htop0 : μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
    by_contra h
    have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr h
    have := htrif hpos
    rw [htri0] at this
    exact (lt_irrefl 0) this
  
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const_uniqueness μ herg
  refine ⟨k, ?_, hk⟩
  
  intro hktop
  rw [hktop] at hk
  rw [hk] at htop0
  exact one_ne_zero htop0

end Percolation
end StatMech
