module
public import Theorem.StatisticalMechanics.Code.Walls.rc69doubledmeasure.Part2
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum
public import Def.StatisticalMechanics.Code.Walls.rc70butterflymeasure.Part2
set_option linter.style.longLine false
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


instance (n : ℕ) (Fam : Finset (Finset (Fin n ⊕ Fin n))) : Decidable (rc70_DisjPreserving n Fam) := by
  unfold rc70_DisjPreserving; infer_instance


end StatMech.Walls
