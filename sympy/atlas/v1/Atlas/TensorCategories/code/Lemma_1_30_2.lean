/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_1_30_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Finiteness.Defs

set_option maxHeartbeats 400000

universe u v

variable (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]

/-- An element of `GL(V)` is unipotent if `g - id` is a nilpotent linear endomorphism. -/
def IsUnipotentElem (g : LinearMap.GeneralLinearGroup k V) : Prop :=
  IsNilpotent (g.val - LinearMap.id)

/-- A subgroup `N ≤ GL(V)` is unipotent if every element is unipotent. -/
def IsUnipotentSubgroup (N : Subgroup (LinearMap.GeneralLinearGroup k V)) : Prop :=
  ∀ g ∈ N, IsUnipotentElem k V g

/-- A subgroup `G ≤ GL(V)` is reductive (in the sense of Definition 1.30.1) if its only
unipotent normal subgroup is trivial. -/
def IsReductiveSubgroup (G : Subgroup (LinearMap.GeneralLinearGroup k V)) : Prop :=
  ∀ N : Subgroup (LinearMap.GeneralLinearGroup k V),
    N ≤ G → N.Normal → IsUnipotentSubgroup k V N → N = ⊥

/-- A submodule `W ≤ V` is invariant under `G ≤ GL(V)` if every element of `G` maps `W` to
itself. -/
def IsInvariantSubmodule
    (G : Subgroup (LinearMap.GeneralLinearGroup k V))
    (W : Submodule k V) : Prop :=
  ∀ g ∈ G, ∀ w ∈ W, (g.val : V →ₗ[k] V) w ∈ W

/-- The defining representation of `G ≤ GL(V)` on `V` is completely reducible if every
`G`-invariant submodule admits a `G`-invariant complement. -/
def IsCompletelyReducibleRep
    (G : Subgroup (LinearMap.GeneralLinearGroup k V)) : Prop :=
  ∀ W : Submodule k V, IsInvariantSubmodule k V G W →
    ∃ W' : Submodule k V, IsInvariantSubmodule k V G W' ∧
      W ⊔ W' = ⊤ ∧ W ⊓ W' = ⊥

/-- The submodule `V^N` of vectors fixed by every element of `N ≤ GL(V)`. -/
def invariantsSubmodule (N : Subgroup (LinearMap.GeneralLinearGroup k V)) : Submodule k V where
  carrier := { w : V | ∀ g ∈ N, (g.val : V →ₗ[k] V) w = w }
  add_mem' := by intro a b ha hb g hg; simp [map_add, ha g hg, hb g hg]
  zero_mem' := by intro g hg; simp [map_zero]
  smul_mem' := by intro c x hx g hg; simp [hx g hg]
