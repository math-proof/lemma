/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc20reflection.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc21persupport
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def rc21_SymmDiffReflection : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∃ K L : Finset (Fin n) → Finset (Fin n),
      (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Disjoint (K S) (L S) ∧
        (∀ T : Finset (Fin n), T ∩ K S = S ∩ K S → T ∈ 𝒜) ∧
        (∀ T : Finset (Fin n), T ∩ L S = S ∩ L S → T ∈ ℬ)) ∧
      Set.InjOn (fun S => symmDiff S (L S)) (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin n)))

end StatMech.Walls
