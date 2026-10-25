/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCoefficientAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexColumnMembershipClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCriticalDivergence.Part4


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


def hlcd_atScale (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) (ts : List ℤ) : Prop :=
  ∃ h : P ts, scale ⟨ts, h⟩ = v


noncomputable def hlcd_atScaleEquiv (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) :
    {ts : List ℤ // hlcd_atScale P scale v ts} ≃
      {i : {ts : List ℤ // P ts} // scale i = v} where
  toFun i := ⟨⟨i.1, i.2.choose⟩, i.2.choose_spec⟩
  invFun i := ⟨i.1.1, ⟨i.1.2, i.2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)


end StatMech.Universality
