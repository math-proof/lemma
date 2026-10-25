/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc19doublecover.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc20reflection.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc20_traceClass (n : ℕ) (K S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  univ.filter (fun T => T ∩ K = S ∩ K)


def rc20_famCylBoxComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter (fun S => decide (∃ K ∈ (univ : Finset (Finset (Fin n))),
    ∃ L ∈ (univ : Finset (Finset (Fin n))), Disjoint K L ∧
      rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n L S ⊆ ℬ) = true)


def rc20_reflInterComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter (fun S => decide (S ∈ 𝒜 ∧ Sᶜ ∈ ℬ) = true)


end StatMech.Walls
