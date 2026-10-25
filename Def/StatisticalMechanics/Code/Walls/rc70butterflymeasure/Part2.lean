/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc69doubledmeasure.Part2
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Theorem.StatisticalMechanics.Code.Walls.rc70butterflymeasure
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc70_DisjPreserving (n : ℕ) (Fam : Finset (Finset (Fin n ⊕ Fin n))) : Prop :=
  ∀ U ∈ Fam, ∀ i : Fin n, ¬ (Sum.inl i ∈ U ∧ Sum.inr i ∈ U)

end StatMech.Walls
