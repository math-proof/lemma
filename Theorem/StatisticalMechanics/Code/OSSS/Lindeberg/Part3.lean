/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Def.StatisticalMechanics.Code.OSSS.Lindeberg.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace Lindeberg

open OSSS.Monotonic OSSS.Coding

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma cExp_eq_cSum_div (μ : ConfigSpace E → ℝ) (F : Finset E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    cExp μ F g ω = cSum μ F g ω / condNorm μ F ω := by
  unfold cExp cSum condMass
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω' _ => ?_)
  by_cases h : Agree F ω ω'
  · simp [h]; ring
  · simp [h]


lemma condNorm_eq_cSum_one (μ : ConfigSpace E → ℝ) (F : Finset E) (ω : ConfigSpace E) :
    condNorm μ F ω = cSum μ F (fun _ => 1) ω := by
  unfold condNorm cSum
  refine Finset.sum_congr rfl (fun ω' _ => ?_)
  by_cases h : Agree F ω ω'
  · simp [h]
  · simp [h]


lemma cSum_split (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E) (he : e ∉ F)
    (g : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    cSum μ F g ω = cSum μ (insert e F) g (setOpen e ω) + cSum μ (insert e F) g (setClosed e ω) := by
  unfold cSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ω' _ => ?_)
  have hne : ∀ x ∈ F, x ≠ e := fun x hxF => by rintro rfl; exact he hxF
  by_cases hF : Agree F ω ω'
  · by_cases hb : ω' e = true
    · have hopen : Agree (insert e F) (setOpen e ω) ω' := by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl | hxF
        · rw [setOpen_self]; exact hb
        · rw [setOpen_of_ne (hne x hxF)]; exact hF x hxF
      have hclosed : ¬ Agree (insert e F) (setClosed e ω) ω' := by
        intro hag; have := hag e (Finset.mem_insert_self e F); rw [setClosed_self] at this
        rw [hb] at this; exact absurd this (by simp)
      rw [if_pos hF, if_pos hopen, if_neg hclosed, add_zero]
    · have hb' : ω' e = false := by cases hh : ω' e; rfl; exact absurd hh hb
      have hclosed : Agree (insert e F) (setClosed e ω) ω' := by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl | hxF
        · rw [setClosed_self]; exact hb'
        · rw [setClosed_of_ne (hne x hxF)]; exact hF x hxF
      have hopen : ¬ Agree (insert e F) (setOpen e ω) ω' := by
        intro hag; have := hag e (Finset.mem_insert_self e F); rw [setOpen_self] at this
        rw [hb'] at this; exact absurd this (by simp)
      rw [if_pos hF, if_neg hopen, if_pos hclosed, zero_add]
  · have h1 : ¬ Agree (insert e F) (setOpen e ω) ω' := by
      intro hag; apply hF; intro x hxF
      have := hag x (Finset.mem_insert_of_mem hxF)
      rwa [setOpen_of_ne (hne x hxF)] at this
    have h2 : ¬ Agree (insert e F) (setClosed e ω) ω' := by
      intro hag; apply hF; intro x hxF
      have := hag x (Finset.mem_insert_of_mem hxF)
      rwa [setClosed_of_ne (hne x hxF)] at this
    rw [if_neg hF, if_neg h1, if_neg h2, add_zero]


lemma cSum_coord_open (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    cSum μ (insert e F) (fun ω'' => g ω'' * coord e ω'') (setOpen e ω)
      = cSum μ (insert e F) g (setOpen e ω) := by
  unfold cSum
  refine Finset.sum_congr rfl (fun ω' _ => ?_)
  simp only []
  by_cases hag : Agree (insert e F) (setOpen e ω) ω'
  · have he : ω' e = true := by
      have := hag e (Finset.mem_insert_self e F); rwa [setOpen_self] at this
    rw [if_pos hag, if_pos hag]; unfold coord; simp [he]
  · rw [if_neg hag, if_neg hag]


lemma cSum_coord_closed (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    cSum μ (insert e F) (fun ω'' => g ω'' * coord e ω'') (setClosed e ω) = 0 := by
  unfold cSum
  refine Finset.sum_eq_zero (fun ω' _ => ?_)
  simp only []
  by_cases hag : Agree (insert e F) (setClosed e ω) ω'
  · have he : ω' e = false := by
      have := hag e (Finset.mem_insert_self e F); rwa [setClosed_self] at this
    rw [if_pos hag]; unfold coord; simp [he]
  · rw [if_neg hag]


lemma cExp_decomp {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (e : E)
    (he : e ∉ F) (f : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    cExp μ F f ω = cExp μ F (coord e) ω * cExp μ (insert e F) f (setOpen e ω)
      + (1 - cExp μ F (coord e) ω) * cExp μ (insert e F) f (setClosed e ω) := by
  have hZopos : 0 < condNorm μ (insert e F) (setOpen e ω) := condNorm_pos hpos _ _
  have hZcpos : 0 < condNorm μ (insert e F) (setClosed e ω) := condNorm_pos hpos _ _
  have hZFpos : 0 < condNorm μ F ω := condNorm_pos hpos _ _
  set Zo := condNorm μ (insert e F) (setOpen e ω) with hZo
  set Zc := condNorm μ (insert e F) (setClosed e ω) with hZc
  set ZF := condNorm μ F ω with hZF
  have hZFsum : ZF = Zo + Zc := by
    rw [hZF, condNorm_eq_cSum_one, cSum_split μ F e he, ← condNorm_eq_cSum_one, ← condNorm_eq_cSum_one]
  have hN : cExp μ F (coord e) ω = Zo / ZF := by
    rw [cExp_eq_cSum_div, cSum_split μ F e he _ ω]
    have ho : cSum μ (insert e F) (coord e) (setOpen e ω) = Zo := by
      have := cSum_coord_open μ F e (fun _ => 1) ω
      simp only [one_mul] at this
      rw [hZo, condNorm_eq_cSum_one, ← this]
    have hc : cSum μ (insert e F) (coord e) (setClosed e ω) = 0 := by
      have := cSum_coord_closed μ F e (fun _ => 1) ω
      simp only [one_mul] at this; exact this
    rw [ho, hc, add_zero]
  have ha : cSum μ (insert e F) f (setOpen e ω) = cExp μ (insert e F) f (setOpen e ω) * Zo := by
    rw [cExp_eq_cSum_div, div_mul_cancel₀]; exact hZopos.ne'
  have hb : cSum μ (insert e F) f (setClosed e ω) = cExp μ (insert e F) f (setClosed e ω) * Zc := by
    rw [cExp_eq_cSum_div, div_mul_cancel₀]; exact hZcpos.ne'
  rw [cExp_eq_cSum_div, cSum_split μ F e he f ω, ha, hb, hN, ← hZF, hZFsum]
  field_simp
  ring


lemma coord_mono (e : E) : Monotone (coord (E := E) e) := by
  intro x y hxy; unfold coord
  by_cases h : x e = true
  · have hy : y e = true := by have := hxy e; rw [h] at this; exact le_antisymm le_top this
    simp [h, hy]
  · simp only [h]
    by_cases h2 : y e = true <;> simp [h2]


lemma coord_nonneg (e : E) : (0 : ConfigSpace E → ℝ) ≤ coord e := by
  intro ω; unfold coord; split <;> norm_num


lemma cExp_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    {g : ConfigSpace E → ℝ} (hg0 : 0 ≤ g) (ω : ConfigSpace E) : 0 ≤ cExp μ F g ω := by
  unfold cExp
  apply Finset.sum_nonneg; intro ω' _
  exact mul_nonneg (hg0 ω')
    (condMass_nonneg (fun x => (hpos x).le) F ω (condNorm_pos hpos F ω) ω')


lemma cExp_le_one {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    {g : ConfigSpace E → ℝ} (hg1 : ∀ ω, g ω ≤ 1) (ω : ConfigSpace E) : cExp μ F g ω ≤ 1 := by
  unfold cExp
  have hsum : ∑ ω', condMass μ F ω ω' = 1 := condMass_sum F ω (condNorm_pos hpos F ω).ne'
  calc ∑ ω', g ω' * condMass μ F ω ω'
      ≤ ∑ ω', 1 * condMass μ F ω ω' := by
        apply Finset.sum_le_sum; intro ω' _
        exact mul_le_mul_of_nonneg_right (hg1 ω')
          (condMass_nonneg (fun x => (hpos x).le) F ω (condNorm_pos hpos F ω) ω')
    _ = 1 := by simp [hsum]


end Lindeberg
end OSSS
end StatMech
