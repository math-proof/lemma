/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeakApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Topology.Instances.Rat
public import Instance.v1.Atlas.ArithmeticGeometry.code.WeakApproximation

@[expose] public section

noncomputable section

open Filter Topology

/-- The absolute value on $\mathbb{Q}$ associated to a place: the $p$-adic absolute value for a
finite place, and the real absolute value $|\cdot|_\infty$ for the infinite place. -/
def PlaceQ.absValue : PlaceQ → AbsoluteValue ℚ ℝ
  | .finite ⟨p, hp⟩ => @Rat.AbsoluteValue.padic p ⟨hp⟩
  | .infinite => Rat.AbsoluteValue.real

end
