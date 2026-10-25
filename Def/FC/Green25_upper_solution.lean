/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Asymptotics Filter Finset


namespace Green25

def Property25 (k N : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ N ∧
  ∀ P : Finpartition (Icc 1 N), #P.parts = k →
  10 * #(P.parts.biUnion Finset.restrictedSumset) ≥ N


noncomputable def bestUpper (N : ℕ) : ℝ := (N : ℝ) / Real.log N


def candidate25 (N : ℕ) : ℕ :=
  max 1 (N / (Nat.log 2 N) ^ 2)


end Green25
