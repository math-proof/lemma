/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Def.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part7
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


@[simp] theorem abigGhostWindowEquiv_none [DecidableEq V] (S : Finset V) :
    (abigGhostWindowEquiv S none : Option V) = none := rfl

@[simp] theorem abigGhostWindowEquiv_some [DecidableEq V] (S : Finset V)
    (x : S) :
    (abigGhostWindowEquiv S (some x) : Option V) = some (x : V) := rfl


end Sharpness
end StatMech
