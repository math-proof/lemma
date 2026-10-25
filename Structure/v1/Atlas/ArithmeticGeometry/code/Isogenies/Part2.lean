/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.EllipticCurves.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.EllipticCurves
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.PadicElliptic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.PadicElliptic
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeierstrassValBound
import Theorem.v1.Atlas.ArithmeticGeometry.code.Isogenies.Part2
open WeierstrassCurve

/-- The function-field extension data associated to an isogeny $\varphi$: a pair of
fields $k(E_1) \supseteq \varphi^* k(E_2)$ with the inclusion as an algebra map. -/


namespace EllipticCurveIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]

end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]

end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]

end EllipticCurveIsogeny

/-- The $p$-adic filtration on $E(\mathbb{Q}_p)$: a decreasing family of
subgroups $E = E_0 \supseteq E_1 \supseteq E_2 \supseteq \cdots$ defined via
the $p$-adic valuation, together with the (mild) assumptions
$a_1 = a_2 = a_3 = 0$ required for the addition-formula computations. -/
structure PadicFiltration (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] where
  group : ℕ → AddSubgroup (W.baseChange ℚ_[p]).toAffine.Point
  antitone : Antitone group
  mem_iff : ∀ n P, P ∈ group n ↔ PadicFiltrationMem W p n P
  zero_eq_top : group 0 = ⊤
  ha₁ : W.a₁ = 0
  ha₂ : W.a₂ = 0
  ha₃ : W.a₃ = 0

