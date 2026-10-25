/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GroundUpWinding


namespace StatMech.Onsager.GroundUp

noncomputable def convexCount {n : ℕ} (t : Fin n → ℤ) : ℕ :=
  (Finset.univ.filter (fun i => t i = 1)).card


noncomputable def reflexCount {n : ℕ} (t : Fin n → ℤ) : ℕ :=
  (Finset.univ.filter (fun i => t i = -1)).card


def turnSum {n : ℕ} (t : Fin n → ℤ) : ℤ := ∑ i, t i


end StatMech.Onsager.GroundUp
