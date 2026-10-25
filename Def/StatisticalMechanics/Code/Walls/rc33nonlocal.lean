/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc32reflwitness.Part2
import Mathlib.Combinatorics.Hall.Basic
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc33_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (R ∈ 𝒜 ∧ Rᶜ ∈ ℬ ∧
    ∃ K ∈ (univ : Finset (Finset (Fin n))), rc20_traceClass n K S ⊆ 𝒜 ∧ R ∩ K = S ∩ K) = true)


def rc33_admOneSidedB (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (R ∈ 𝒜 ∧ Rᶜ ∈ ℬ ∧
    ∃ L ∈ (univ : Finset (Finset (Fin n))), rc20_traceClass n L S ⊆ ℬ ∧ Rᶜ ∩ L = S ∩ L) = true)


def rc33_admBothSided (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (R ∈ 𝒜 ∧ Rᶜ ∈ ℬ ∧
    (∃ K ∈ (univ : Finset (Finset (Fin n))), rc20_traceClass n K S ⊆ 𝒜 ∧ R ∩ K = S ∩ K) ∧
    (∃ L ∈ (univ : Finset (Finset (Fin n))), rc20_traceClass n L S ⊆ ℬ ∧ Rᶜ ∩ L = S ∩ L)) = true)


end StatMech.Walls
