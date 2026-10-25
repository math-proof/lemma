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
import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part2


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- Reflexivity of the Pic equivalence relation on homogeneous fractions. -/
lemma HomogFraction.PicEquiv.rfl' (σ : Type*) (k : Type*) [Field k]
    (p : HomogFraction σ k) : p.PicEquiv σ k p :=
  ⟨1, 1, 0, 0, one_ne_zero, one_ne_zero,
   isHomogeneous_one σ k, isHomogeneous_one σ k,
   rfl, Associated.refl _⟩

/-- Symmetry of the Pic equivalence relation. -/
lemma HomogFraction.PicEquiv.symm' (σ : Type*) (k : Type*) [Field k]
    {p q : HomogFraction σ k}
    (h : p.PicEquiv σ k q) : q.PicEquiv σ k p := by
  obtain ⟨a, b, da, db, ha, hb, hah, hbh, hd, hass⟩ := h
  exact ⟨b, a, db, da, hb, ha, hbh, hah, hd.symm, hass.symm⟩

/-- Transitivity of the Pic equivalence relation. -/
lemma HomogFraction.PicEquiv.trans' (σ : Type*) (k : Type*) [Field k]
    {p q r : HomogFraction σ k}
    (h1 : p.PicEquiv σ k q) (h2 : q.PicEquiv σ k r) :
    p.PicEquiv σ k r := by
  obtain ⟨a₁, b₁, da₁, db₁, ha₁, hb₁, ha₁h, hb₁h, hd₁, hass₁⟩ := h1
  obtain ⟨a₂, b₂, da₂, db₂, ha₂, hb₂, ha₂h, hb₂h, hd₂, hass₂⟩ := h2
  refine ⟨a₁ * a₂, b₁ * b₂, da₁ + da₂, db₁ + db₂,
    mul_ne_zero ha₁ ha₂, mul_ne_zero hb₁ hb₂,
    ha₁h.mul ha₂h, hb₁h.mul hb₂h, by omega, ?_⟩
  have h1' := hass₁.mul_right (b₂ * r.den)
  have h2' := hass₂.mul_right (a₁ * p.den)
  have heq1 : q.num * a₁ * p.den * (b₂ * r.den) =
    q.num * b₂ * r.den * (a₁ * p.den) := by ring
  rw [heq1] at h1'
  have h3 := h1'.trans h2'
  have heq2 : p.num * b₁ * q.den * (b₂ * r.den) =
    q.den * (p.num * (b₁ * b₂) * r.den) := by ring
  have heq3 : r.num * a₂ * q.den * (a₁ * p.den) =
    q.den * (r.num * (a₁ * a₂) * p.den) := by ring
  rw [heq2, heq3] at h3
  exact Associated.of_mul_left h3 (Associated.refl _) q.den_ne

end PicardProjective
end
