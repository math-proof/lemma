/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneDual.Part3
import Theorem.StatisticalMechanics.Code.Walls.rb3reimerclose.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc4_core
import Theorem.StatisticalMechanics.Code.Walls.rc3_keyflipinvolutive
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

open StatMech.Walls

open StatMech.Walls.Reimer

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem kss_sum_four_comm {A B C D R : Type*} [AddCommMonoid R]
    (sA : Finset A) (sB : Finset B) (sC : Finset C) (sD : Finset D)
    (f : A → B → C → D → R) :
    (∑ a ∈ sA, ∑ b ∈ sB, ∑ c ∈ sC, ∑ d ∈ sD, f a b c d) =
      ∑ c ∈ sC, ∑ d ∈ sD, ∑ a ∈ sA, ∑ b ∈ sB, f a b c d := by
  calc
    (∑ a ∈ sA, ∑ b ∈ sB, ∑ c ∈ sC, ∑ d ∈ sD, f a b c d) =
        ∑ a ∈ sA, ∑ c ∈ sC, ∑ b ∈ sB, ∑ d ∈ sD, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c ∈ sC, ∑ a ∈ sA, ∑ b ∈ sB, ∑ d ∈ sD, f a b c d := by
      rw [Finset.sum_comm]
    _ = ∑ c ∈ sC, ∑ a ∈ sA, ∑ d ∈ sD, ∑ b ∈ sB, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c ∈ sC, ∑ d ∈ sD, ∑ a ∈ sA, ∑ b ∈ sB, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]


end StatMech.FrontierA
