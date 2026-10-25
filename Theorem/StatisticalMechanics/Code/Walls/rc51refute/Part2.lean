/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc50hall.Part3
import Def.StatisticalMechanics.Code.Walls.rc51refute.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


open Classical in


theorem rc51_hallCondComp_iff (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc51_hallCondComp n 𝒜 ℬ = true ↔ rc49_HallCond 𝒜 ℬ := by
  rw [rc51_hallCondComp, decide_eq_true_eq, rc49_HallCond]
  have hbox : rc20_famCylBoxComp n 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := rc20_famCylBoxComp_eq n 𝒜 ℬ
  have hnb : ∀ W : Finset (Finset (Fin n)),
      W.biUnion (rc51_neighbourhoodComp n 𝒜 ℬ) = W.biUnion (rc49_neighbourhood 𝒜 ℬ) :=
    fun W => Finset.biUnion_congr rfl (fun S _ => rc51_neighbourhoodComp_eq n 𝒜 ℬ S)
  constructor
  · intro h W hW
    have hWmem : W ∈ (rc20_famCylBoxComp n 𝒜 ℬ).powerset := by
      rw [Finset.mem_powerset, hbox]; exact hW
    have := h W hWmem
    rwa [hnb] at this
  · intro h W hW
    rw [Finset.mem_powerset, hbox] at hW
    have := h W hW
    rwa [hnb]

open Classical in


theorem rc51_not_hallCond_of_comp_false (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc51_hallCondComp n 𝒜 ℬ = false) : ¬ rc49_HallCond 𝒜 ℬ := by
  intro hHall
  rw [← rc51_hallCondComp_iff] at hHall
  rw [hHall] at h
  exact Bool.noConfusion h


end StatMech.Walls
