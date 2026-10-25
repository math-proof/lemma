/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part3


namespace StatMech.Universality

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager


def HexBrickInteriorOnLeft {n : ℕ} [NeZero n]
    (heading : Fin n → Fin 6) : Prop :=
  StatMech.Onsager.Orientation.leftParity
    (fun i => hexBrickDir (heading i)) 0 = 1


end StatMech.Universality
