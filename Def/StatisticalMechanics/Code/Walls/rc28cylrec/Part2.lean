/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc27recursion.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc28cylrec
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc28_traceClassE (n : ℕ) (E K S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  E.powerset.filter (fun T => T ∩ K = S ∩ K)


def rc28_famCylBoxEComp (n : ℕ) (E : Finset (Fin n)) (𝒜 ℬ : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  E.powerset.filter (fun S => decide (∃ K ∈ E.powerset, ∃ L ∈ E.powerset, Disjoint K L ∧
    rc28_traceClassE n E K S ⊆ 𝒜 ∧ rc28_traceClassE n E L S ⊆ ℬ) = true)


end StatMech.Walls
