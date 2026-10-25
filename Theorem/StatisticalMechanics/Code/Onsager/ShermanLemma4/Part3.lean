/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Def.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part2


namespace StatMech.Onsager

open Matrix BigOperators Finset

section Orbit

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} [NeZero n]


theorem ons_iterate_inv {f : (Fin n → E) → ℂ}
    (hf : ∀ v, f (ons_cyclicShift v) = f v) (v : Fin n → E) (j : ℕ) :
    f (ons_cyclicShift^[j] v) = f v := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', hf, ih]


theorem ons_eq_of_rel {f : (Fin n → E) → ℂ}
    (hf : ∀ v, f (ons_cyclicShift v) = f v) {v w : Fin n → E}
    (h : (ons_orbitSetoid E n).r v w) : f v = f w := by
  obtain ⟨j, hj⟩ := h
  have := ons_iterate_inv hf v j
  rw [hj] at this
  exact this.symm


theorem ons_sum_fiberwise_orbit {f : (Fin n → E) → ℂ}
    (hf : ∀ v, f (ons_cyclicShift v) = f v) :
    ∑ v : Fin n → E, f v
      = ∑ r : Fin n → E, (ons_orbitCard r : ℂ) * f r := by
  have key : ∀ r : Fin n → E,
      (∑ v ∈ Finset.univ.filter (fun v => ons_rep v = r), f v)
        = (ons_orbitCard r : ℂ) * f r := by
    intro r
    have h1 : (∑ v ∈ Finset.univ.filter (fun v => ons_rep v = r), f v)
        = ∑ _v ∈ Finset.univ.filter (fun v => ons_rep v = r), f r := by
      apply Finset.sum_congr rfl
      intro v hv
      have hrep : ons_rep v = r := (Finset.mem_filter.mp hv).2
      have hval : f (ons_rep v) = f v := ons_eq_of_rel hf (ons_rep_rel v)
      rw [← hval, hrep]
    rw [h1, Finset.sum_const, nsmul_eq_mul]
    rfl
  calc
    ∑ v : Fin n → E, f v
        = ∑ r : Fin n → E, ∑ v ∈ Finset.univ.filter (fun v => ons_rep v = r), f v :=
          (Finset.sum_fiberwise Finset.univ ons_rep f).symm
    _ = ∑ r : Fin n → E, (ons_orbitCard r : ℂ) * f r :=
          Finset.sum_congr rfl (fun r _ => key r)


theorem ons_sum_loopWeight_orbit (Λ : Matrix E E ℂ) :
    ∑ v : Fin n → E, ons_loopWeight Λ v
      = ∑ r : Fin n → E, (ons_orbitCard r : ℂ) * ons_loopWeight Λ r :=
  ons_sum_fiberwise_orbit (ons_loopWeight_cyclicShift Λ)

end Orbit

section LogTail

open Complex


theorem ons_hasSum_shifted_pow_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / (k + 1)) (-Complex.log (1 - z)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  
  have h2 := (hasSum_nat_add_iff' (f := fun n : ℕ => z ^ n / (n : ℂ)) 1).mpr h
  simpa using h2


theorem ons_tsum_shifted_pow_div {z : ℂ} (hz : ‖z‖ < 1) :
    ∑' k : ℕ, z ^ (k + 1) / (k + 1) = -Complex.log (1 - z) :=
  (ons_hasSum_shifted_pow_div hz).tsum_eq

end LogTail
end StatMech.Onsager
