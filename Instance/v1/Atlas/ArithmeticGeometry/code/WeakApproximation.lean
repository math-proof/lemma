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
public import Inductive.v1.Atlas.ArithmeticGeometry.code.WeakApproximation

@[expose] public section

noncomputable section

open Filter Topology

/-- Decidable equality on places of $\mathbb{Q}$: two places are either both infinite, or finite
with the same prime. -/
instance : DecidableEq PlaceQ := by
  intro a b
  cases a with
  | finite p =>
    cases b with
    | finite q =>
      exact if h : p = q then isTrue (by rw [h]) else
        isFalse (by intro heq; exact h (PlaceQ.finite.inj heq))
    | infinite => exact isFalse PlaceQ.noConfusion
  | infinite =>
    cases b with
    | finite _ => exact isFalse PlaceQ.noConfusion
    | infinite => exact isTrue rfl

end
