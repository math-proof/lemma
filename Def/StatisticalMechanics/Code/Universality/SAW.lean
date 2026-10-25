/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/SAW.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.Universality

open Filter Topology

open scoped Topology


def Submultiplicative (c : ℕ → ℝ) : Prop :=
  ∀ m n, c (m + n) ≤ c m * c n


end StatMech.Universality
