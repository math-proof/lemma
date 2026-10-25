/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralDecayClose.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.FK.CylinderDecayClose.Part4
open MeasureTheory Filter Topology BoundedContinuousFunction SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


theorem cdc_decayFun_monomial_wired_tendsto_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_wiredMultiHomogeneous hp hp1 g) (s : Finset (Sym2 (Site d))) :
    Tendsto (isd_decayFun (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
        g (cdc_monomialBcf s)) atTop (𝓝 0) := by
  
  have hdecay : isd_decayFun
      (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
      g (cdc_monomialBcf s)
    = fun n => (wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent s)
        - (wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))) := by
    funext n; exact cdc_decayFun_monomial _ g s n
  rw [hdecay]
  
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  obtain ⟨N', t', hst'⟩ := cdc_finset_in_box (s.image (fun e => g⁻¹ • e))
  
  have h1full := cdc_wired_multiOpenEvent_tendsto N t hp hp1
  rw [← hst] at h1full
  have h2full := cdc_wired_multiOpenEvent_tendsto N' t' hp hp1
  rw [← hst'] at h2full
  
  have h1 := h1full.comp hφ.tendsto_atTop
  have h2 := h2full.comp hφ.tendsto_atTop
  
  have hsub := h1.sub h2
  rw [← hhom s, sub_self] at hsub
  exact hsub


theorem cdc_decayFun_monomial_free_tendsto_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_freeMultiHomogeneous hp hp1 g) (s : Finset (Sym2 (Site d))) :
    Tendsto (isd_decayFun (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
        g (cdc_monomialBcf s)) atTop (𝓝 0) := by
  have hdecay : isd_decayFun
      (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
      g (cdc_monomialBcf s)
    = fun n => (freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent s)
        - (freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))) := by
    funext n; exact cdc_decayFun_monomial _ g s n
  rw [hdecay]
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  obtain ⟨N', t', hst'⟩ := cdc_finset_in_box (s.image (fun e => g⁻¹ • e))
  have h1full := cdc_free_multiOpenEvent_tendsto N t hp hp1
  rw [← hst] at h1full
  have h2full := cdc_free_multiOpenEvent_tendsto N' t' hp hp1
  rw [← hst'] at h2full
  have h1 := h1full.comp hφ.tendsto_atTop
  have h2 := h2full.comp hφ.tendsto_atTop
  have hsub := h1.sub h2
  rw [← hhom s, sub_self] at hsub
  exact hsub


theorem cdc_monomialCM_empty : cdc_monomialCM (∅ : Finset (Sym2 (Site d))) = 1 := by
  unfold cdc_monomialCM
  rw [Finset.prod_empty]


theorem cdc_monomialCM_singleton (e : Sym2 (Site d)) :
    cdc_monomialCM ({e} : Finset (Sym2 (Site d))) = idc_coordCM e := by
  unfold cdc_monomialCM
  rw [Finset.prod_singleton]


theorem cdc_monomialCM_mul (s₁ s₂ : Finset (Sym2 (Site d))) :
    cdc_monomialCM s₁ * cdc_monomialCM s₂ = cdc_monomialCM (s₁ ∪ s₂) := by
  apply ContinuousMap.ext
  intro ω
  simp only [ContinuousMap.mul_apply, cdc_monomialCM_apply, cdc_prod_coordCM_eq_indicator]
  have hinter : cdc_multiOpenEvent (s₁ ∪ s₂)
      = cdc_multiOpenEvent s₁ ∩ cdc_multiOpenEvent s₂ := by
    ext ω'
    simp only [cdc_multiOpenEvent, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_union]
    constructor
    · intro h; exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩
    · rintro ⟨h1, h2⟩ e (he | he)
      · exact h1 e he
      · exact h2 e he
  rw [hinter]
  have := Set.inter_indicator_mul (s := cdc_multiOpenEvent s₁) (t := cdc_multiOpenEvent s₂)
    (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) ω
  simp only [mul_one] at this
  rw [this]


theorem cdc_closure_isMonomial {h : C(ConfigSpace (Sym2 (Site d)), ℝ)}
    (hh : h ∈ Submonoid.closure (Set.range (idc_coordCM (d := d)))) :
    ∃ s : Finset (Sym2 (Site d)), h = cdc_monomialCM s := by
  induction hh using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    exact ⟨{e}, (cdc_monomialCM_singleton e).symm⟩
  | one => exact ⟨∅, (cdc_monomialCM_empty).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s₁, rfl⟩ := hx
    obtain ⟨s₂, rfl⟩ := hy
    exact ⟨s₁ ∪ s₂, cdc_monomialCM_mul s₁ s₂⟩


theorem cdc_decayFun_add (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (f f' : ConfigSpace (Sym2 (Site d)) →ᵇ ℝ) (n : ℕ) :
    isd_decayFun μ g (f + f') n = isd_decayFun μ g f n + isd_decayFun μ g f' n := by
  simp only [isd_decayFun, BoundedContinuousFunction.coe_add, Pi.add_apply]
  have h1 : (∫ x, (f x + f' x) ∂(μ n : Measure _))
      = (∫ x, f x ∂(μ n : Measure _)) + ∫ x, f' x ∂(μ n : Measure _) :=
    integral_add (f.integrable _) (f'.integrable _)
  have h2 : (∫ x, (f (shift g x) + f' (shift g x)) ∂(μ n : Measure _))
      = (∫ x, f (shift g x) ∂(μ n : Measure _)) + ∫ x, f' (shift g x) ∂(μ n : Measure _) :=
    integral_add ((f.compContinuous ⟨shift g, continuous_shift g⟩).integrable _)
      ((f'.compContinuous ⟨shift g, continuous_shift g⟩).integrable _)
  rw [h1, h2]
  ring


theorem cdc_decayFun_smul (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (c : ℝ) (f : ConfigSpace (Sym2 (Site d)) →ᵇ ℝ) (n : ℕ) :
    isd_decayFun μ g (c • f) n = c * isd_decayFun μ g f n := by
  simp only [isd_decayFun, BoundedContinuousFunction.coe_smul, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]
  ring


theorem cdc_decayFun_zero (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (n : ℕ) :
    isd_decayFun μ g (0 : ConfigSpace (Sym2 (Site d)) →ᵇ ℝ) n = 0 := by
  simp only [isd_decayFun, BoundedContinuousFunction.coe_zero, Pi.zero_apply, integral_zero,
    sub_zero]


end FK
end StatMech
