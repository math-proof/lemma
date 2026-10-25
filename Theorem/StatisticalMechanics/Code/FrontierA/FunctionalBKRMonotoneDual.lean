/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneReal.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterfly
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem sum_four_comm {A B C D R : Type*} [AddCommMonoid R]
    (sA : Finset A) (sB : Finset B) (sC : Finset C) (sD : Finset D)
    (f : A → B → C → D → R) :
    (Finset.sum sA fun a => Finset.sum sB fun b =>
      Finset.sum sC fun c => Finset.sum sD fun d => f a b c d) =
      Finset.sum sC fun c => Finset.sum sD fun d =>
        Finset.sum sA fun a => Finset.sum sB fun b => f a b c d := by
  calc
    (Finset.sum sA fun a => Finset.sum sB fun b =>
        Finset.sum sC fun c => Finset.sum sD fun d => f a b c d) =
        Finset.sum sA fun a => Finset.sum sC fun c =>
          Finset.sum sB fun b => Finset.sum sD fun d => f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = Finset.sum sC fun c => Finset.sum sA fun a =>
        Finset.sum sB fun b => Finset.sum sD fun d => f a b c d := by
      rw [Finset.sum_comm]
    _ = Finset.sum sC fun c => Finset.sum sA fun a =>
        Finset.sum sD fun d => Finset.sum sB fun b => f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = Finset.sum sC fun c => Finset.sum sD fun d =>
        Finset.sum sA fun a => Finset.sum sB fun b => f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

theorem sum_three_comm {A B C R : Type*} [AddCommMonoid R]
    (sA : Finset A) (sB : Finset B) (sC : Finset C)
    (f : A → B → C → R) :
    (Finset.sum sA fun a => Finset.sum sB fun b =>
      Finset.sum sC fun c => f a b c) =
      Finset.sum sB fun b => Finset.sum sC fun c =>
        Finset.sum sA fun a => f a b c := by
  calc
    (Finset.sum sA fun a => Finset.sum sB fun b =>
        Finset.sum sC fun c => f a b c) =
        Finset.sum sB fun b => Finset.sum sA fun a =>
          Finset.sum sC fun c => f a b c := by
      rw [Finset.sum_comm]
    _ = Finset.sum sB fun b => Finset.sum sC fun c =>
        Finset.sum sA fun a => f a b c := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]


end StatMech.FrontierA
