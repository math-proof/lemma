module
public import Theorem.StatisticalMechanics.Code.Walls.rc57witnessed.Part4
public import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
public import Mathlib.Combinatorics.Hall.Basic
public import Theorem.StatisticalMechanics.Code.Walls.rc58bipartiteflow
set_option linter.style.longLine false
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc58_kadm (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (rc20_reflInterComp n 𝒜 ℬ).filter (fun R => decide (∃ K ∈ (univ : Finset (Finset (Fin n))),
    rc20_traceClass n K S ⊆ 𝒜 ∧ R ∩ K = S ∩ K) = true)

end StatMech.Walls
