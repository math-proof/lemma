module
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace DiscreteValuation

variable {R : Type*} [CommRing R] (v : DiscreteValuation R)

omit hp in
/-- Compatibility of the projections: the reduction $\mathbb{Z}/p^n\mathbb{Z} \to
\mathbb{Z}/p^m\mathbb{Z}$ composed with `invLimProj p n` equals `invLimProj p m` for $m \le n$. -/
theorem invLimProj_compat (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (invLimProj p n) =
      invLimProj p m := by
  ext ⟨a, ha⟩
  simp only [invLimProj, RingHom.comp_apply, Pi.evalRingHom_apply, Subring.coe_subtype]
  exact ha m n h

end DiscreteValuation
