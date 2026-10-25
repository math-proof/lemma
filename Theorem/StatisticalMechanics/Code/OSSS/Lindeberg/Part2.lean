/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Def.StatisticalMechanics.Code.OSSS.Lindeberg.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace Lindeberg

open OSSS.Monotonic OSSS.Coding

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma cExp_Fmeas (μ : ConfigSpace E → ℝ) (F : Finset E) (g : ConfigSpace E → ℝ) :
    Fmeas F (cExp μ F g) := by
  intro η η' h
  unfold cExp condMass
  rw [condNorm_congr μ F η η' h]
  apply Finset.sum_congr rfl; intro ω' _
  congr 2
  exact if_congr (agree_congr_of_eq_on F η η' ω' h) rfl rfl


lemma cExp_pullout {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (g h : ConfigSpace E → ℝ) (hh : Fmeas F h) :
    (∑ ω, (cExp μ F g ω * h ω) * μ ω) = ∑ ω, (g ω * h ω) * μ ω := by
  unfold cExp condMass
  have step : ∀ ω, ((∑ ω', g ω' * ((if Agree F ω ω' then μ ω' else 0) / condNorm μ F ω)) * h ω) * μ ω
      = ∑ ω', (if Agree F ω ω' then (g ω' * h ω') * μ ω' else 0) * (μ ω / condNorm μ F ω) := by
    intro ω
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro ω' _
    by_cases hag : Agree F ω ω'
    · rw [if_pos hag, if_pos hag]
      have : h ω = h ω' := hh ω ω' (fun fe hfe => (hag fe hfe).symm)
      rw [this]; ring
    · rw [if_neg hag, if_neg hag]; ring
  simp_rw [step]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro ω' _
  have hZeq : ∀ ω, Agree F ω ω' → condNorm μ F ω = condNorm μ F ω' := by
    intro ω hag; apply condNorm_congr; intro fe hfe; exact (hag fe hfe).symm
  have hrw : (∑ ω, (if Agree F ω ω' then (g ω' * h ω') * μ ω' else 0) * (μ ω / condNorm μ F ω))
      = ((g ω' * h ω') * μ ω' / condNorm μ F ω') * ∑ ω, (if Agree F ω ω' then μ ω else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ω _
    by_cases hag : Agree F ω ω'
    · rw [if_pos hag, if_pos hag, hZeq ω hag]; ring
    · rw [if_neg hag, if_neg hag]; ring
  rw [hrw]
  have hcn : (∑ ω, (if Agree F ω ω' then μ ω else 0)) = condNorm μ F ω' := by
    unfold condNorm; apply Finset.sum_congr rfl; intro ω _
    exact if_congr ⟨fun hh fe hfe => (hh fe hfe).symm, fun hh fe hfe => (hh fe hfe).symm⟩ rfl rfl
  rw [hcn]
  have hZ := condNorm_pos hpos F ω'
  field_simp


lemma mean_cExp {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (g : ConfigSpace E → ℝ) :
    mean μ (cExp μ F g) = mean μ g := by
  unfold mean
  have h1 := cExp_pullout hpos F g (fun _ => 1) (fun _ _ _ => rfl)
  simpa using h1


lemma cExp_mono {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hFKG : FKGLatticeCondition μ)
    (F : Finset E) {g : ConfigSpace E → ℝ} (hg : Monotone g) (hg0 : 0 ≤ g) :
    Monotone (cExp μ F g) := by
  intro ω ω' hle
  have hμ : 0 ≤ μ := fun x => (hpos x).le
  have hle' : ∀ f ∈ F, ω f ≤ ω' f := fun f _ => hle f
  have hZω := condNorm_pos hpos F ω
  have hZω' := condNorm_pos hpos F ω'
  exact holley_inequality
    (condMass_nonneg hμ F ω hZω) (condMass_nonneg hμ F ω' hZω')
    (by rw [condMass_sum F ω hZω.ne', condMass_sum F ω' hZω'.ne'])
    (cross_condMass hμ hFKG F ω ω' hle' hZω hZω')
    hg hg0


lemma mean_mul_ge {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) {A B : ConfigSpace E → ℝ}
    (hA : Monotone A) (hB : Monotone B) :
    mean μ A * mean μ B ≤ mean μ (fun ω => A ω * B ω) := by
  have h := fkg_inequality (π := μ) (fun ω => (hpos ω).le) hμ1 hFKG hA hB
  
  have e1 : (∑ ω, μ ω * A ω) = mean μ A := by
    unfold mean; exact Finset.sum_congr rfl (fun ω _ => by ring)
  have e2 : (∑ ω, μ ω * B ω) = mean μ B := by
    unfold mean; exact Finset.sum_congr rfl (fun ω _ => by ring)
  have e3 : (∑ ω, μ ω * (A ω * B ω)) = mean μ (fun ω => A ω * B ω) := by
    unfold mean; exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [e1, e2, e3] at h
  exact h


end Lindeberg
end OSSS
end StatMech
