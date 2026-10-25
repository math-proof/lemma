/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerCapacity
import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Structure.StatisticalMechanics.Code.SLE.ChainCapacity
open Complex Set Filter Topology MeasureTheory
open scoped NNReal


namespace StatMech.SLE

lemma IsCapacityParametrized.coeff_zero {c : LoewnerChain} {a₁ : ℝ → ℝ}
    (h : IsCapacityParametrized c a₁) : a₁ 0 = 0 := by
  have hid : HasHalfPlaneCapacity (c.maps 0) 0 :=
    hasHalfPlaneCapacity_zero_of_eq_id (fun z => c.maps_zero z)
  exact (h.normalized 0 Set.self_mem_Ici).unique hid


end StatMech.SLE
