/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part4


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- Multiplication of homogeneous fractions respects the Pic equivalence relation. -/
lemma mul_compat (σ : Type*) (k : Type*) [Field k]
    {p₁ p₂ q₁ q₂ : HomogFraction σ k}
    (hp : p₁.PicEquiv σ k p₂) (hq : q₁.PicEquiv σ k q₂) :
    (p₁.mul σ k q₁).PicEquiv σ k (p₂.mul σ k q₂) := by
  obtain ⟨ap, bp, dap, dbp, hap, hbp, haph, hbph, hdp, hassp⟩ := hp
  obtain ⟨aq, bq, daq, dbq, haq, hbq, haqh, hbqh, hdq, hassq⟩ := hq
  refine ⟨ap * aq, bp * bq, dap + daq, dbp + dbq,
    mul_ne_zero hap haq, mul_ne_zero hbp hbq,
    haph.mul haqh, hbph.mul hbqh, by omega, ?_⟩
  obtain ⟨u₁, hu₁⟩ := hassp
  obtain ⟨u₂, hu₂⟩ := hassq
  exact ⟨u₁ * u₂, by
    simp only [HomogFraction.mul, Units.val_mul]
    calc p₁.num * q₁.num * (bp * bq) * (p₂.den * q₂.den) * (↑u₁ * ↑u₂)
        = (p₁.num * bp * p₂.den * ↑u₁) * (q₁.num * bq * q₂.den * ↑u₂) := by ring
      _ = (p₂.num * ap * p₁.den) * (q₂.num * aq * q₁.den) := by rw [hu₁, hu₂]
      _ = p₂.num * q₂.num * (ap * aq) * (p₁.den * q₁.den) := by ring⟩

/-- Inversion of homogeneous fractions respects the Pic equivalence relation. -/
lemma inv_compat (σ : Type*) (k : Type*) [Field k]
    {p q : HomogFraction σ k}
    (h : p.PicEquiv σ k q) : (p.inv σ k).PicEquiv σ k (q.inv σ k) := by
  obtain ⟨a, b, da, db, ha, hb, hah, hbh, hd, hass⟩ := h
  refine ⟨b, a, db, da, hb, ha, hbh, hah, hd.symm, ?_⟩
  simp only [HomogFraction.inv]
  obtain ⟨u, hu⟩ := hass.symm
  exact ⟨u, by
    calc p.den * a * q.num * ↑u
        = q.num * a * p.den * ↑u := by ring
      _ = p.num * b * q.den := hu
      _ = q.den * b * p.num := by ring⟩

end PicardProjective
end
