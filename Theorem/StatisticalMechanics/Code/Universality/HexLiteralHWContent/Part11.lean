module
public import Mathlib
public import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
public import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
public import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part11


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


theorem hhc_literalHighest_partial_bound (a : ℂ) (h0 : ℤ) (N : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (∑ s ∈ (hhc_literalHighestDecomp a h0 N).lowerImage,
          hhc_halfWeight x s) *
        (∑ s ∈ (hhc_literalHighestDecomp a h0 N).upperImage,
          hhc_halfWeight x s) := by
  rw [← hhc_partial_eq a h0 x N]
  exact (hhc_literalHighestDecomp a h0 N).finite_content_bound hx


end StatMech.Universality
