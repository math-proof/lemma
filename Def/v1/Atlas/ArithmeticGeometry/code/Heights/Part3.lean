/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisPlaceHelper
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisPlaceHelper
import Structure.v1.Atlas.ArithmeticGeometry.code.Heights


noncomputable section

open Height MvPolynomial

namespace AbsoluteHeight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Empty.Finite ι]

attribute [instance] TwoIsogenyData.instAddCommGroup

attribute [instance] TwoIsogenyData.instDescentTargetGroup

attribute [instance] TwoIsogenyData.instDescentTarget'Group

attribute [instance] TwoIsogenyData.descentMap_range_finite

attribute [instance] TwoIsogenyData.descentMap'_range_finite

def IsNonzeroSquare (q : ℚ) : Prop := ∃ r : ℚ, r ≠ 0 ∧ q = r ^ 2


def E'Curve (a b : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0; a₂ := -2 * a; a₃ := 0; a₄ := a ^ 2 - 4 * b; a₆ := 0

noncomputable def descentMapRaw (a b : ℚ) (hdisc : a ^ 2 - 4 * b ≠ 0) :
    (E'Curve a b).toAffine.Point → Additive (ℚˣ ⧸ Subgroup.square ℚˣ) :=
  fun P => match P with
  | .zero => Additive.ofMul 1
  | .some x _y _hxy =>
    if hx : x = 0 then
      Additive.ofMul (QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (a ^ 2 - 4 * b) hdisc))
    else
      Additive.ofMul (QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 x hx))

def canonicalHeightSeq (h : E → ℝ) (P : E) (n : ℕ) : ℝ :=
  h ((2 ^ n : ℤ) • P) / (4 : ℝ) ^ n

def canonicalHeight (h : E → ℝ) (P : E) : ℝ :=
  limUnder atTop (canonicalHeightSeq h P)

end AbsoluteHeight
end
