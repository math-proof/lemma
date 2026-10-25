/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.OrderClosed
open scoped BigOperators
open Real Set Finset Filter Topology

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Integration

theorem slope_ge_of_deriv_ge (a b m : ℝ) (hab : a ≤ b) (T T' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt T (T' x) x)
    (hbound : ∀ x ∈ Icc a b, m ≤ T' x) :
    m * (b - a) ≤ T b - T a := by
  
  set h : ℝ → ℝ := fun x => T x - m * x with hh
  have hhderiv : ∀ x ∈ Icc a b, HasDerivAt h (T' x - m) x := by
    intro x hx
    have h2 : HasDerivAt (fun x : ℝ => m * x) m x := hasDerivAt_const_mul m
    convert (hd x hx).sub h2 using 1
  have hmono : MonotoneOn h (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hhderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hhderiv x (mem_Icc_of_Ioo hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hhderiv x (mem_Icc_of_Ioo hx)).deriv]
      have hmle : m ≤ T' x := hbound x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      linarith
  have hkey : h a ≤ h b := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  rw [hh] at hkey
  simp only [] at hkey
  nlinarith [hkey]


theorem logStep_le (S f : ℝ) (hS : 0 < S) (hf : 0 ≤ f) :
    Real.log (S + f) - Real.log S ≤ f / S := by
  have hSf : 0 < S + f := by linarith
  rw [← Real.log_div (ne_of_gt hSf) (ne_of_gt hS)]
  have h1 : Real.log ((S + f) / S) ≤ (S + f) / S - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : (S + f) / S - 1 = f / S := by field_simp; ring
  linarith


theorem logStep_sum_le_sum_deriv (fseq fpseq Sig : ℕ → ℝ) (n : ℕ)
    (hSrec : ∀ i, Sig (i + 1) = Sig i + fseq i)
    (hfnn : ∀ i, 1 ≤ i → 0 ≤ fseq i)
    (hSpos : ∀ i, 1 ≤ i → 0 < Sig i)
    (hdiff : ∀ i : ℕ, 1 ≤ i → ((i : ℝ) / Sig i) * fseq i ≤ fpseq i) :
    Real.log (Sig (n + 1)) - Real.log (Sig 1)
      ≤ ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i / (i : ℝ) := by
  
  have hstep : ∀ i ∈ Finset.Ico 1 (n + 1),
      (Real.log (Sig (i + 1)) - Real.log (Sig i)) ≤ fpseq i / (i : ℝ) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi1 : 1 ≤ i := hi.1
    have hipos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
    have hSi : 0 < Sig i := hSpos i hi1
    have hfi : 0 ≤ fseq i := hfnn i hi1
    
    have hlog : Real.log (Sig (i + 1)) - Real.log (Sig i) ≤ fseq i / Sig i := by
      rw [hSrec i]; exact logStep_le (Sig i) (fseq i) hSi hfi
    
    have hdi : fseq i / Sig i ≤ fpseq i / (i : ℝ) := by
      have hd := hdiff i hi1
      rw [div_mul_eq_mul_div, div_le_iff₀ hSi] at hd
      rw [div_le_div_iff₀ hSi hipos]
      nlinarith [hd]
    linarith
  refine le_trans ?_ (Finset.sum_le_sum hstep)
  
  have htel : ∑ i ∈ Finset.Ico 1 (n + 1), (Real.log (Sig (i + 1)) - Real.log (Sig i))
      = Real.log (Sig (n + 1)) - Real.log (Sig 1) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    have hcongr : ∀ x ∈ Finset.range n,
        (Real.log (Sig (1 + x + 1)) - Real.log (Sig (1 + x)))
          = (fun j => Real.log (Sig (j + 1 + 1)) - Real.log (Sig (j + 1))) x := by
      intro x _; ring_nf
    rw [Finset.sum_congr rfl hcongr]
    simpa using Finset.sum_range_sub (fun j => Real.log (Sig (j + 1))) n
  rw [htel]


end OSSS.Integration
end StatMech
