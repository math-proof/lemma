module
public import Theorem.StatisticalMechanics.Code.Walls.rc68countmarriage.Part3
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
public import Theorem.StatisticalMechanics.Code.Walls.rc69doubledmeasure
set_option linter.style.longLine false
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc69_DoubledMeasureResidue : Prop := rc60_BoxUnionBound


end StatMech.Walls
