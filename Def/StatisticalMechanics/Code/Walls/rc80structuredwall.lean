/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc79toporbit.Part4
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def rc80_occ (A : Finset (ConfigSpace ι)) (K : Finset ι) (w : ConfigSpace ι) : Bool :=
  decide (∀ w' : ConfigSpace ι, (∀ e ∈ K, w' e = w e) → w' ∈ A)


def rc80_disjOccG (A B : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  Finset.univ.filter (fun w =>
    ∃ K L : Finset ι, Disjoint K L ∧ rc80_occ A K w = true ∧ rc80_occ B L w = true)


def rc80_compl (w : ConfigSpace ι) : ConfigSpace ι := fun i => !w i


def rc80_reflInterG (A B : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  A.filter (fun a => rc80_compl a ∈ B)


def rc80_IsUpper (A : Finset (ConfigSpace ι)) : Prop :=
  ∀ a ∈ A, ∀ i : ι, (Function.update a i true) ∈ A


def rc80_IsLower (A : Finset (ConfigSpace ι)) : Prop :=
  ∀ a ∈ A, ∀ i : ι, (Function.update a i false) ∈ A


def rc80_minext (K : Finset ι) (w : ConfigSpace ι) : ConfigSpace ι :=
  fun i => if i ∈ K then w i else false


def rc80_maxext (L : Finset ι) (w : ConfigSpace ι) : ConfigSpace ι :=
  fun i => if i ∈ L then w i else true


end StatMech.Walls
