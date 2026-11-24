module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
public import Def.StatisticalMechanics.Code.SLE.Cardy.Part7
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.SLE

lemma IsCLEParameter.pos {κ : ℝ} (h : IsCLEParameter κ) : 0 < κ := by
  have : (0:ℝ) < 8 / 3 := by norm_num
  exact lt_trans this h.1


end StatMech.SLE
