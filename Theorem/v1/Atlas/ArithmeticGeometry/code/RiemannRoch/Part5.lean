/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite
import Def.v1.Atlas.ArithmeticGeometry.code.EffectiveDivisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.EffectiveDivisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CanonicalDivisors
import Def.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors.Part2
import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part5
open scoped RestrictedProduct

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}


/-- Membership in $\mathcal{L}(D)$ unfolded: $f \in \mathcal{L}(D)$ iff $f = 0$ or
$\operatorname{div}(f) + D$ is effective. -/
theorem mem_riemannRochSpace_iff (D : CurveDivisor C) (f : F) :
    f ∈ riemannRochSpace (k := k) D ↔
      f = 0 ∨ ∃ (hf : f ≠ 0),
        (principalDivisor (Units.mk0 f hf) + D).IsEffective :=
  Iff.rfl

/-- Multiplication by a unit $f$ with $\operatorname{div}(f) = A - B$ sends
$\mathcal{L}(A)$ into $\mathcal{L}(B)$. -/
lemma mul_unit_mem_riemannRochSpace (A B : CurveDivisor C) (f : Fˣ)
    (hf : principalDivisor f = A - B)
    (g : F) (hg : g ∈ riemannRochSpace (k := k) A) :
    (f : F) * g ∈ riemannRochSpace (k := k) B := by
  rw [mem_riemannRochSpace_iff] at hg ⊢
  by_cases hg0 : g = 0
  · left; simp [hg0]
  · right
    have hfg_ne : (f : F) * g ≠ 0 := mul_ne_zero f.ne_zero hg0
    refine ⟨hfg_ne, fun P => ?_⟩
    obtain ⟨hg_ne, heff⟩ := hg.resolve_left hg0
    have heffP := heff P
    simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply] at heffP ⊢
    have key : Units.mk0 ((f : F) * g) hfg_ne = f * Units.mk0 g hg_ne := by
      apply Units.ext; simp
    rw [key, ord_mul]
    have hAP : A P = ord P f + B P := by
      have := congr_fun (congr_arg DFunLike.coe hf) P
      simp only [Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply] at this
      linarith
    linarith

