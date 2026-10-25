/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
open Finset MeasureTheory
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {α : Type*}


def leftBlock : Set (α ⊕ α) := {x | x.isLeft}


def rightBlock : Set (α ⊕ α) := {x | x.isRight}


end StatMech
