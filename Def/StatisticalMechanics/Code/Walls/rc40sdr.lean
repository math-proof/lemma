/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc40sdr
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc40_R0valuesComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (univ.filter (fun KL : Finset (Fin n) × Finset (Fin n) =>
      decide (Disjoint KL.1 KL.2 ∧ rc20_traceClass n KL.1 S ⊆ 𝒜 ∧
        rc20_traceClass n KL.2 S ⊆ ℬ) = true)).image
    (fun KL => rc36_R0 S KL.1 KL.2)


end StatMech.Walls
