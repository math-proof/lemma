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
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.EllipticCurves
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.PadicElliptic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Theorem.v1.Atlas.ArithmeticGeometry.code.PadicElliptic
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.WeierstrassValBound
public import Instance.v1.Atlas.ArithmeticGeometry.code.Isogenies.Part3
open WeierstrassCurve


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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

/-- Membership in the $n$-th piece of the $p$-adic filtration on $E(\mathbb{Q}_p)$:
the point $O$ is always in, and an affine point $(x, y)$ lies in $E_n$ when $n = 0$
or when $y \neq 0$ and $v_p(x) - v_p(y) \geq n$. -/
def PadicFiltrationMem (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (P : (W.baseChange ℚ_[p]).toAffine.Point) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => n = 0 ∨ (y ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x - Padic.valuation y)


