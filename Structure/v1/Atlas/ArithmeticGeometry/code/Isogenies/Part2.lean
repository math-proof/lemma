/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Def.v1.Atlas.ArithmeticGeometry.code.EllipticCurves.Part7
public import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.EllipticCurves
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.PadicElliptic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Theorem.v1.Atlas.ArithmeticGeometry.code.PadicElliptic
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.WeierstrassValBound
public import Theorem.v1.Atlas.ArithmeticGeometry.code.Isogenies.Part2
public section

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

