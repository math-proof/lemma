/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc86consolidation
import Def.StatisticalMechanics.Code.Walls.rb3reimerclose.Part2
open Finset
open scoped BigOperators NNReal


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false

set_option linter.unusedSimpArgs false


open Classical in


lemma rb3_witK_spec {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    (∀ T : Finset (Fin n), T ∩ (rb3_witK 𝒜 ℬ S) = S ∩ (rb3_witK 𝒜 ℬ S) → T ∈ 𝒜) ∧
    (∀ T : Finset (Fin n), T ∩ (rb3_witK 𝒜 ℬ S)ᶜ = S ∩ (rb3_witK 𝒜 ℬ S)ᶜ → T ∈ ℬ) := by
  rw [rc20_famCylBox, Finset.mem_filter] at hS
  have hex : ∃ K L : Finset (Fin n), Disjoint K L ∧
      (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) := hS.2
  have hK : rb3_witK 𝒜 ℬ S = hex.choose := by rw [rb3_witK, dif_pos hex]
  obtain ⟨L, hKL, hKA, hLB⟩ := hex.choose_spec
  rw [hK]
  refine ⟨hKA, ?_⟩
  
  intro T hT
  apply hLB
  
  have hLsub : L ⊆ hex.chooseᶜ := by
    intro i hiL
    rw [Finset.mem_compl]
    exact Finset.disjoint_right.mp hKL hiL
  
  rw [rb3_inter_eq_iff_agree] at hT ⊢
  exact fun i hiL => hT i (hLsub hiL)


end StatMech.Walls.Reimer
