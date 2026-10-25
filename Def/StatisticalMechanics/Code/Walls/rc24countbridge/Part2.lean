/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc23boxmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc24countbridge.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def rc24_BoxDownUpMono : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
    #(rc20_famCylBox 𝒜 ℬ)
      ≤ #(rc20_famCylBox (Down.compression i 𝒜) (rc22_upComp i ℬ))


def rc24_upCompComp (n : ℕ) (i : Fin n) (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (Down.compression i (𝒜.image (fun S => Sᶜ))).image (fun S => Sᶜ)


end StatMech.Walls
