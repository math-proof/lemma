/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerODE
import Def.StatisticalMechanics.Code.SLE.LoewnerProps.Part2
open Complex Set Filter Topology
open scoped NNReal ComplexConjugate


namespace StatMech.SLE

lemma HasCapacityRate.hcap_zero {g : ℝ → ℂ → ℂ} {a : ℝ} (h : HasCapacityRate g a) :
    HasHalfPlaneCapacity (g 0) 0 := by
  have := h 0 Set.self_mem_Ici; rwa [mul_zero] at this


theorem hcap_linear_of_decomposition {gs gincr gt : ℂ → ℂ} {cs ct : ℝ}
    (hcompose : gt = gincr ∘ gs)
    (hs : HasHalfPlaneCapacity gs cs)
    (hincr : HasHalfPlaneCapacity gincr (ct - cs)) :
    HasHalfPlaneCapacity gt ct := by
  rw [hcompose]
  have := hasHalfPlaneCapacity_comp hs hincr
  rwa [add_sub_cancel] at this


end StatMech.SLE
