/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc70butterflymeasure.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc71disjpreserving
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


def rc71_IsBoxDoubled (Fam : Finset (Finset (Fin n ⊕ Fin n))) : Prop :=
  ∃ 𝒜' ℬ' : Finset (Finset (Fin n)), StatMech.boxDoubled 𝒜' ℬ' = Fam

end StatMech.Walls
