/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoStrandSplit


namespace StatMech.FrontierD

theorem exists_prefix_length_sum_eq_one
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (hsum : steps.sum = 2) :
    exists cut : Nat, cut <= steps.length /\
      (steps.take cut).sum = 1 := by
  obtain ⟨first, second, hsplit, hfirst, _⟩ :=
    exists_two_unit_sum_arcs_of_sum_eq_two steps hsteps hsum
  refine ⟨first.length, ?_, ?_⟩
  · rw [hsplit, List.length_append]
    omega
  · rw [hsplit, List.take_left]
    exact hfirst


end StatMech.FrontierD
