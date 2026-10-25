/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc50hall.Part3
import Def.StatisticalMechanics.Code.Walls.rc51refute
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


open Classical in

theorem rc51_neighbourhoodComp_eq (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc51_neighbourhoodComp n 𝒜 ℬ S = rc49_neighbourhood 𝒜 ℬ S := by
  ext R
  rw [rc51_neighbourhoodComp, rc49_neighbourhood, Finset.mem_filter, Finset.mem_filter,
    decide_eq_true_eq, rc20_reflInterComp_eq]
  refine and_congr_right (fun _ => ?_)
  constructor
  · rintro ⟨K, _, L, _, hKL, hKA, hLB, hEq⟩
    exact ⟨K, L, hKL, (rc20_traceClass_subset_iff n K S 𝒜).mp hKA,
      (rc20_traceClass_subset_iff n L S ℬ).mp hLB, hEq⟩
  · rintro ⟨K, L, hKL, hKA, hLB, hEq⟩
    exact ⟨K, Finset.mem_univ _, L, Finset.mem_univ _, hKL,
      (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA,
      (rc20_traceClass_subset_iff n L S ℬ).mpr hLB, hEq⟩


end StatMech.Walls
