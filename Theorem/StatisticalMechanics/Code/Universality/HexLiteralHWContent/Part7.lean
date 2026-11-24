module
public import Mathlib
public import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
public import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
public import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hhc_literal_partial_bound (a : ℂ) (h0 : ℤ) (N : ℕ)
    (lower upper : hhc_Dn a h0 N → HexHWContentHalf)
    (hreconstruct : ∀ d, d.1 = hhc_halfTurns (lower d) ++ hhc_halfTurns (upper d))
    {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (∑ s ∈ (hhc_literalDecomp a h0 N lower upper hreconstruct).lowerImage,
          hhc_halfWeight x s) *
        (∑ s ∈ (hhc_literalDecomp a h0 N lower upper hreconstruct).upperImage,
          hhc_halfWeight x s) := by
  rw [← hhc_partial_eq a h0 x N]
  exact (hhc_literalDecomp a h0 N lower upper hreconstruct).finite_content_bound hx


end StatMech.Universality
