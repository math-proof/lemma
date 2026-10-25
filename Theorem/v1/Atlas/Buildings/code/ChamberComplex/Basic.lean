/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.Basic.Part3
variable {V : Type*} [DecidableEq V]


/-- Self-distance is zero: $d(C,C) = 0$. -/
theorem galleryDist_self (K : SimplicialComplex V) (C : Finset V) :
    galleryDist K C C = 0 := by
  unfold galleryDist
  simp

