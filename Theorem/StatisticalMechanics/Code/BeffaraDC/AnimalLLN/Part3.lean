/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.BeffaraDC.AnimalLLN.Part3


namespace StatMech

namespace BeffaraDC

open Finset Filter Topology

open scoped Topology

variable {V : Type*} [DecidableEq V] [Fintype V]


theorem subGreedyAnimalValue_le {𝒜 : ℕ → Finset (Finset V)} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (o : V) (hsub : ∀ n, 𝒜 n ⊆ animalsLE o n) (n : ℕ) :
    subGreedyAnimalValue 𝒜 w n ≤ greedyAnimalValue w o n := by
  rw [subGreedyAnimalValue]
  split
  · rename_i h
    refine Finset.sup'_le h _ (fun S hS => ?_)
    rw [greedyAnimalValue, dif_pos (h.mono (hsub n))]
    exact Finset.le_sup' (fun S => ∑ v ∈ S, w v) (hsub n hS)
  · exact greedyAnimalValue_nonneg hw o n


theorem subGreedyAnimalValue_le_card_mul {𝒜 : ℕ → Finset (Finset V)} {w : V → ℝ}
    {M : ℝ} (hw : ∀ v, 0 ≤ w v) (hM : ∀ v, w v ≤ M) (hM0 : 0 ≤ M) (o : V)
    (hsub : ∀ n, 𝒜 n ⊆ animalsLE o n) (n : ℕ) :
    subGreedyAnimalValue 𝒜 w n ≤ M * n :=
  (subGreedyAnimalValue_le hw o hsub n).trans (greedyAnimalValue_le_card_mul hM hM0 o n)

end BeffaraDC
end StatMech
