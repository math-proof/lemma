/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.VectorTwoPoint
import Theorem.StatisticalMechanics.Code.Probability.KKLInequality.Part4
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Def.StatisticalMechanics.Code.Probability.KKLfromHC.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] [DecidableEq ι] in

@[simp] theorem khc_walshChar_empty (x : ι → Bool) :
    khc_walshChar (∅ : Finset ι) x = 1 := by
  simp [khc_walshChar]

omit [Fintype ι] [DecidableEq ι] in

theorem khc_walshChar_sq (S : Finset ι) (x : ι → Bool) :
    (khc_walshChar S x) ^ 2 = 1 := by
  unfold khc_walshChar
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one (fun i _ => by rw [sq]; exact khc_sign_sq (x i))


theorem khc_walshChar_as_univ (S : Finset ι) (x : ι → Bool) :
    khc_walshChar S x = ∏ i : ι, (if i ∈ S then khc_sign (x i) else 1) := by
  unfold khc_walshChar; rw [Finset.prod_ite_mem, Finset.univ_inter]


theorem khc_walshChar_mul (S T : Finset ι) (x : ι → Bool) :
    khc_walshChar S x * khc_walshChar T x = khc_walshChar (symmDiff S T) x := by
  rw [khc_walshChar_as_univ, khc_walshChar_as_univ, khc_walshChar_as_univ,
      ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT, Finset.mem_symmDiff, khc_sign_sq]


theorem khc_uexp_walshChar (S : Finset ι) :
    bnt_uexp (khc_walshChar S) = if S = ∅ then 1 else 0 := by
  unfold bnt_uexp khc_walshChar
  have hchar : ∀ x : ι → Bool, (∏ i ∈ S, khc_sign (x i))
      = ∏ i : ι, (if i ∈ S then khc_sign (x i) else 1) := by
    intro x; rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp only [khc_sign] at hchar ⊢
  simp_rw [hchar]
  rw [← Fintype.prod_sum (fun (i : ι) (c : Bool) =>
    if i ∈ S then (if c then (-1 : ℝ) else 1) else 1)]
  have hfac : ∀ i : ι, (∑ c : Bool, if i ∈ S then (if c then (-1 : ℝ) else 1) else 1)
      = (if i ∈ S then 0 else 2) := by
    intro i; by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [hfac]
  by_cases hS : S = ∅
  · subst hS
    simp only [Finset.notMem_empty, if_false, if_true]
    rw [Finset.prod_const, Finset.card_univ, div_self (by positivity)]
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_div]


theorem khc_orthonormal (S T : Finset ι) :
    bnt_uexp (fun x => khc_walshChar S x * khc_walshChar T x) = if S = T then 1 else 0 := by
  simp_rw [khc_walshChar_mul]
  rw [khc_uexp_walshChar]
  by_cases h : S = T
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hsd
    exact h (symmDiff_eq_bot.mp (by simpa using hsd))


omit [DecidableEq ι] in


theorem khc_sum_walshChar_mul (x y : ι → Bool) :
    (∑ S : Finset ι, khc_walshChar S x * khc_walshChar S y)
      = if x = y then (2 ^ Fintype.card ι : ℝ) else 0 := by
  have hpt : ∀ S : Finset ι, khc_walshChar S x * khc_walshChar S y
      = ∏ i ∈ S, (khc_sign (x i) * khc_sign (y i)) := by
    intro S; unfold khc_walshChar; rw [← Finset.prod_mul_distrib]
  simp_rw [hpt]
  have hpow : (univ : Finset (Finset ι)) = (univ : Finset ι).powerset := by ext S; simp
  rw [hpow, ← Finset.prod_one_add]
  have hfac : ∀ i : ι, (1 + khc_sign (x i) * khc_sign (y i)) = if x i = y i then (2 : ℝ) else 0 := by
    intro i; cases hxi : x i <;> cases hyi : y i <;> simp [khc_sign] <;> norm_num
  simp_rw [hfac]
  by_cases hxy : x = y
  · subst hxy; simp only [if_true]; rw [Finset.prod_const, Finset.card_univ]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])


end Probability
end StatMech
