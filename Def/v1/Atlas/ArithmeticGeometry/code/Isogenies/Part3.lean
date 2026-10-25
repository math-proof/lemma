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
import Theorem.v1.Atlas.ArithmeticGeometry.code.Isogenies.Part3
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

/-- The $n$-th level $E_n$ of the $p$-adic filtration, packaged as an additive
subgroup of $E(\mathbb{Q}_p)$. -/
def padicFiltrationGroup (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (ha₁ : W.a₁ = 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0)
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    AddSubgroup (W.baseChange ℚ_[p]).toAffine.Point where
  carrier := {P | PadicFiltrationMem W p n P}
  zero_mem' := PadicFiltrationMem.zero W p n
  add_mem' ha hb := PadicFiltrationMem.add_mem ha₁ ha₂ ha₃ ha hb
  neg_mem' ha := PadicFiltrationMem.neg_mem ha₁ ha₃ ha

/-- Predicate: an affine point $P = (x, y) \in E(\mathbb{Q}_p)$ has
$p$-adically integral coordinates, i.e. $v_p(x) \geq 0$ and $v_p(y) \geq 0$
(the point at infinity is vacuously integral). -/
def CoordinatesPadicIntegral {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [Fact (Nat.Prime p)]
    (P : (W.baseChange ℚ_[p]).toAffine.Point) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => 0 ≤ Padic.valuation x ∧ 0 ≤ Padic.valuation y

