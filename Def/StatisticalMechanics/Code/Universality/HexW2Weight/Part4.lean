/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part3


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


def hexW2_singleRight_memD : List ℤ → Prop := fun ts => ts = [(-1 : ℤ)]


def hexW2_singleRight_elt : {ts // hexW2_singleRight_memD ts} := ⟨[(-1 : ℤ)], rfl⟩


end StatMech.Universality
