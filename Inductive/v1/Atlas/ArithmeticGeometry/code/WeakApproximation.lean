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


noncomputable section

open Filter Topology

/-- A *place of $\mathbb{Q}$* is either the archimedean (real) place or a $p$-adic place for some
prime $p$. -/
public inductive PlaceQ where
  | finite (p : Nat.Primes) : PlaceQ
  | infinite : PlaceQ

end
