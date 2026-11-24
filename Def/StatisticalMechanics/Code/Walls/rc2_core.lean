module
public import Theorem.StatisticalMechanics.Code.Walls.rc2_slabcardallisbridge
public import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
public import Theorem.StatisticalMechanics.Code.Walls.rc2_cardformiffinter
public import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
public import Theorem.StatisticalMechanics.Code.Walls.rc2_doubledboxcount.Part2
public import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
public import Theorem.StatisticalMechanics.Code.Walls.rc2_core
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def SlabInjection (A B : Set (ConfigSpace α)) : Prop :=
  ∀ k : ConfigSpace α × ConfigSpace α,
    ∃ f : ConfigSpace α → ConfigSpace α,
      Set.InjOn f {ω | ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k} ∧
      ∀ ω, ω ∈ disjointOccurrence A B → ω ∈ rc2_slab k →
        f ω ∈ A ∩ rc2_keyReflect k B ∧ f ω ∈ rc2_slab k

end StatMech.Walls
