module
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardProjective
public import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part7
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.AdjoinRoot
public import Instance.v1.Atlas.AlgebraicGeometryI.code.ConicRational.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConicRational.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace ConicRational

section General

variable (R : Type*) [CommRing R]

/-- Over a field, the powers of `X` are non-zero-divisors in `k[X]`. -/
theorem powers_X_le_nonZeroDivisors :
    Submonoid.powers (Polynomial.X : Polynomial k) ≤ nonZeroDivisors (Polynomial k) := by
  intro x ⟨n, hn⟩
  rw [mem_nonZeroDivisors_iff_ne_zero, ← hn]
  exact pow_ne_zero n Polynomial.X_ne_zero

end General
end ConicRational
