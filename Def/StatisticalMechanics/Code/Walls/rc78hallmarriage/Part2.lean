/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc77configmeasure.Part4
import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc78_colTypeF (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) : Fin 2 → Bool × Bool :=
  fun i => (p.1 i && p.2 i, p.1 i || p.2 i)


end StatMech.Walls
