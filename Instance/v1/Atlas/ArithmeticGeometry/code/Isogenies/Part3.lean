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
import Structure.v1.Atlas.ArithmeticGeometry.code.Isogenies
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

open scoped Classical in
/-- Variant of Corollary 24.10 over an algebraic closure: $E(\bar k)[n]$ is finite. -/
noncomputable instance baseChange_padic_isElliptic
    {p : ℕ} [Fact (Nat.Prime p)]
    {W : WeierstrassCurve ℚ} [W.IsElliptic] :
    (W.baseChange ℚ_[p]).IsElliptic := by
  constructor
  rw [show (W.baseChange ℚ_[p]).Δ = algebraMap ℚ ℚ_[p] W.Δ by
    simp [WeierstrassCurve.baseChange, WeierstrassCurve.Δ]]
  exact (algebraMap ℚ ℚ_[p]).isUnit_map ‹W.IsElliptic›.isUnit

