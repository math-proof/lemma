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
import Theorem.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part3
open scoped RestrictedProduct

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}


/-- The order at $P$ packaged as a multiplicative monoid homomorphism
$F^\times \to \mathbb{Z}$ (written multiplicatively). -/
noncomputable def CurveWithOrd.ordMonoidHom {C : Type*} {F : Type*} [Field F]
    [CurveWithOrd C F] (P : C) : Fˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (CurveWithOrd.ord P f)
  map_one' := by
    have : CurveWithOrd.ord P (1 : Fˣ) = 0 := by
      have h := CurveWithOrd.ord_mul P (1 : Fˣ) 1
      simp at h; linarith
    simp [this]
  map_mul' f g := by
    rw [CurveWithOrd.ord_mul P f g, ofAdd_add]

