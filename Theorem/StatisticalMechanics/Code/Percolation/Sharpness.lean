/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem gronwall_dct (f f' : ℝ → ℝ) (a p : ℝ) (ha0 : 0 < a) (hap : a < p) (hp1 : p < 1)
    (hcont : ContinuousOn f (Icc a p))
    (hub : ∀ t ∈ Icc a p, f t ≤ 1)
    (hfa : 0 ≤ f a)
    (hderiv : ∀ t ∈ Ioo a p, HasDerivAt f (f' t) t)
    (hdiff_ineq : ∀ t ∈ Ioo a p, f' t ≥ (1 / (t * (1 - t))) * (1 - f t)) :
    f p ≥ (p - a) / (p * (1 - a)) := by
  have h1tpos : ∀ t ∈ Icc a p, (0 : ℝ) < 1 - t := fun t ht => by
    have : t ≤ p := ht.2; linarith
  
  set g : ℝ → ℝ := fun t => (1 - f t) * (t / (1 - t)) with hg
  have hμcont : ContinuousOn (fun t => t / (1 - t)) (Icc a p) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; exact (h1tpos t ht).ne'
  have hgcont : ContinuousOn g (Icc a p) := ContinuousOn.mul (by fun_prop) hμcont
  have hint : interior (Icc a p) = Ioo a p := interior_Icc
  
  have hgderiv : ∀ t ∈ Ioo a p, HasDerivAt g
      (-(f' t) * (t / (1 - t)) + (1 - f t) * (1 / (1 - t) ^ 2)) t := by
    intro t ht
    have h1t : (0 : ℝ) < 1 - t := by have := ht.2; linarith
    have hfd : HasDerivAt (fun t => 1 - f t) (-(f' t)) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).sub (hderiv t ht)
    have hμd : HasDerivAt (fun t => t / (1 - t)) (1 / (1 - t) ^ 2) t := by
      have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
        simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
      have := h1.div h2 h1t.ne'
      convert this using 1; field_simp; ring
    exact hfd.mul hμd
  
  have hgderiv_nonpos : ∀ t ∈ Ioo a p,
      (-(f' t) * (t / (1 - t)) + (1 - f t) * (1 / (1 - t) ^ 2)) ≤ 0 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans ha0 ht.1
    have h1t : (0 : ℝ) < 1 - t := by have := ht.2; linarith
    have htIcc : t ∈ Icc a p := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hfle : f t ≤ 1 := hub t htIcc
    have hdi := hdiff_ineq t ht
    have hμpos : (0 : ℝ) ≤ t / (1 - t) := by positivity
    have key : (1 / (t * (1 - t))) * (1 - f t) * (t / (1 - t)) = (1 - f t) * (1 / (1 - t) ^ 2) := by
      field_simp
    have step : (1 / (t * (1 - t))) * (1 - f t) * (t / (1 - t)) ≤ f' t * (t / (1 - t)) :=
      mul_le_mul_of_nonneg_right hdi hμpos
    rw [key] at step
    nlinarith [step]
  
  have hgmono : AntitoneOn g (Icc a p) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a p) hgcont
    · rw [hint]; intro t ht; exact (hgderiv t ht).differentiableAt.differentiableWithinAt
    · rw [hint]; intro t ht; rw [(hgderiv t ht).deriv]; exact hgderiv_nonpos t ht
  
  have hgle : g p ≤ g a :=
    hgmono ⟨le_refl a, le_of_lt hap⟩ ⟨le_of_lt hap, le_refl p⟩ (le_of_lt hap)
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hppos : (0 : ℝ) < p := lt_trans ha0 hap
  have hga_le : g a ≤ a / (1 - a) := by
    rw [hg]; simp only
    have hμa : (0 : ℝ) ≤ a / (1 - a) := by positivity
    nlinarith [hfa, hμa]
  have hcomb : (1 - f p) * (p / (1 - p)) ≤ a / (1 - a) := le_trans hgle hga_le
  have hkey : (1 - f p) * p / (1 - p) ≤ a / (1 - a) := by rw [← mul_div_assoc] at hcomb; exact hcomb
  rw [div_le_div_iff₀ h1p h1a] at hkey
  rw [ge_iff_le, div_le_iff₀ (by positivity)]
  nlinarith [hkey]


end Percolation
end StatMech
