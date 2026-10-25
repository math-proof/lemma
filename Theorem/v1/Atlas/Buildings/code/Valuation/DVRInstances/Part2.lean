/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Def.v1.Atlas.Buildings.code.Valuation.DVRInstances
open DVRContext

variable (p : ℕ) [Fact (Nat.Prime p)]


noncomputable section

set_option maxHeartbeats 32000000

variable {p} (n : ℕ) (hn : 0 < n)

/-- *Membership in the $p$-adic valuation subring via norm*: $x \in \mathbb{Z}_p$ (as image
of `embed`) iff $\|x\|_p \le 1$. -/
theorem padic_isInO_iff (x : ℚ_[p]) :
    (padicDVRContext p n hn).isInO x ↔ ‖x‖ ≤ 1 := by
  constructor
  · rintro ⟨r, hr⟩; rw [← hr]; exact PadicInt.norm_le_one r
  · intro h; exact ⟨⟨x, h⟩, rfl⟩

/-- *Membership in the $p$-adic maximal ideal via norm*: $x \in p\mathbb{Z}_p$ iff
$\|x\|_p < 1$. Uses `PadicInt.norm_lt_one_iff_dvd` to translate between divisibility by $p$
and norm being strictly less than $1$. -/
theorem padic_isInMaxIdeal_iff (x : ℚ_[p]) :
    (padicDVRContext p n hn).isInMaxIdeal x ↔ ‖x‖ < 1 := by
  constructor
  · rintro ⟨r, hr_mem, hr_eq⟩
    rw [← hr_eq]
    have hdvd : (p : ℤ_[p]) ∣ r := by
      rw [DVRContext.maxIdeal, Ideal.mem_span_singleton] at hr_mem; exact hr_mem
    exact (PadicInt.norm_lt_one_iff_dvd r).mpr hdvd
  · intro h
    have hle : ‖x‖ ≤ 1 := le_of_lt h
    let r : ℤ_[p] := ⟨x, hle⟩
    have hr_dvd : (p : ℤ_[p]) ∣ r := (PadicInt.norm_lt_one_iff_dvd r).mp h
    refine ⟨r, ?_, rfl⟩
    rw [DVRContext.maxIdeal, Ideal.mem_span_singleton]; exact hr_dvd

/-- *Units of $\mathbb{Z}_p$ via norm*: $x \in \mathbb{Z}_p^\times$ iff $\|x\|_p = 1$. -/
theorem padic_isUnitInO_iff (x : ℚ_[p]) :
    (padicDVRContext p n hn).isUnitInO x ↔ ‖x‖ = 1 := by
  constructor
  · rintro ⟨r, hr_unit, hr_eq⟩; rw [← hr_eq]; exact PadicInt.isUnit_iff.mp hr_unit
  · intro h; exact ⟨⟨x, le_of_eq h⟩, PadicInt.isUnit_iff.mpr h, rfl⟩

/-- *Iwahori matrices over $\mathbb{Q}_p$ have unit determinant*: phrased in the abstract
`DVRContext` language as a wrapper around `iwahori_det_norm_eq_one`. -/
theorem padic_iwahori_det_unit (g : Matrix (Fin n) (Fin n) ℚ_[p])
    (hdiag : ∀ i, (padicDVRContext p n hn).isUnitInO (g i i))
    (habove : ∀ i j, i < j → (padicDVRContext p n hn).isInO (g i j))
    (hbelow : ∀ i j, j < i → (padicDVRContext p n hn).isInMaxIdeal (g i j)) :
    (padicDVRContext p n hn).isUnitInO g.det := by
  rw [padic_isUnitInO_iff]
  have hdiag' : ∀ i, ‖g i i‖ = 1 := fun i => (padic_isUnitInO_iff n hn _).mp (hdiag i)
  have habove' : ∀ i j, i < j → ‖g i j‖ ≤ 1 :=
    fun i j h => (padic_isInO_iff n hn _).mp (habove i j h)
  have hbelow' : ∀ i j, j < i → ‖g i j‖ < 1 :=
    fun i j h => (padic_isInMaxIdeal_iff n hn _).mp (hbelow i j h)
  exact iwahori_det_norm_eq_one p g hdiag' habove' hbelow'

end
