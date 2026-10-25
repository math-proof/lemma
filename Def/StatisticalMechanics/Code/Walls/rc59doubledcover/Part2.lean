/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc33nonlocal.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc56sandwich.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc59doubledcover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


noncomputable def rc59_doubledCover (𝒯 : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → Finset (Fin n)) : Finset (Finset (Fin n ⊕ Fin n)) :=
  𝒯.image (fun S => rc59_dblPair S (f S))


end StatMech.Walls
