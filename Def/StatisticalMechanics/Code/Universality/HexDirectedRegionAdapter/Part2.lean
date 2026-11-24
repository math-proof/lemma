module
public import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk


def hexStripMembershipDRegion (M : Finset ℂ) : ℂ → ℤ → Prop :=
  fun m _ => m ∈ M


end StatMech.Universality
