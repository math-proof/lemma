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
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


noncomputable def rc70_wt (n : ℕ) (q : ℚ) (U : Finset (Fin n ⊕ Fin n)) : ℚ :=
  q ^ U.card * (1 - q) ^ (2 * n - U.card)


noncomputable def rc70_measure (n : ℕ) (q : ℚ) (Fam : Finset (Finset (Fin n ⊕ Fin n))) : ℚ :=
  Fam.sum (rc70_wt n q)


end StatMech.Walls
