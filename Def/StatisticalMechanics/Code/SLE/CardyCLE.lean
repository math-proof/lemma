/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
public import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part8

@[expose] public section

open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

def HasConformalRadius (z : ℂ) (φ : ℂ → ℂ) (r : ℝ) : Prop :=
  φ 0 = z ∧ HasDerivAt φ (r : ℂ) 0 ∧ 0 < r


noncomputable def discConformalRadius (r : ℝ) : ℝ := r

end StatMech.SLE
