module
public import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
public import Theorem.StatisticalMechanics.Code.Inequalities.Reimer
open MeasureTheory Finset
open scoped NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

open ConfigSpace

variable {E F : Type*}


def flipCfg (ω : ConfigSpace E) : ConfigSpace E := fun x => !(ω x)

end StatMech
