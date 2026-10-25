/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexBoundary


namespace StatMech.Universality

open Complex Filter Topology

open scoped Topology Real BigOperators


lemma hexBdryCl_pos : 0 < hexBdryCl := by
  unfold hexBdryCl
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]


lemma hexBdryCt_pos : 0 < hexBdryCt := by
  unfold hexBdryCt; rw [Real.cos_pi_div_four]; positivity


lemma hexBdryCl_eq : hexBdryCl = Real.cos (3 * Real.pi / 8) := rfl


lemma hexBdryCt_eq : hexBdryCt = Real.cos (Real.pi / 4) := rfl


end StatMech.Universality
