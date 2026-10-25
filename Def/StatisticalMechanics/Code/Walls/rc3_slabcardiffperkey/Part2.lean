/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabcardallisbridge
import Theorem.StatisticalMechanics.Code.Walls.rc3_slabcardiffperkey.Part2
open Finset
open scoped FinsetFamily NNReal


namespace StatMech.Walls

open StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc3_PerKeyAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))) (k : ConfigSpace (Fin n) × ConfigSpace (Fin n)),
    rc3_PerKey A B k


end StatMech.Walls
