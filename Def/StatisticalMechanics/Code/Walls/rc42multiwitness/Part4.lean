/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc42multiwitness.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc42_traceSliceComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (K S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (rc20_reflInterComp n 𝒜 ℬ).filter (fun R => R ∩ K = S ∩ K)


def rc42_admCoveringComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (rc42_cwits n 𝒜 ℬ S).biUnion (fun K => rc42_traceSliceComp n 𝒜 ℬ K S)

end StatMech.Walls
