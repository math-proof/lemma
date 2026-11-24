module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
public import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
public import Structure.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager


namespace HexAWBrickCycle

def heading {n : ℕ} [NeZero n] (C : HexAWBrickCycle n) : Fin n → Fin 6 :=
  fun i => hexAWHeadingMod (C.coord i) (C.edge i)


def direction {n : ℕ} [NeZero n] (C : HexAWBrickCycle n) : Fin n → Fin 4 :=
  fun i => hexBrickDir (C.heading i)

end HexAWBrickCycle
end StatMech.Universality
