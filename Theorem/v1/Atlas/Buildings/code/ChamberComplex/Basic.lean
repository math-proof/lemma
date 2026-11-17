/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Def.v1.Atlas.Buildings.code.ChamberComplex.Basic.Part3

public section

variable {V : Type*} [DecidableEq V]


/-- Self-distance is zero: $d(C,C) = 0$. -/
theorem galleryDist_self (K : SimplicialComplex V) (C : Finset V) :
    galleryDist K C C = 0 := by
  unfold galleryDist
  simp

