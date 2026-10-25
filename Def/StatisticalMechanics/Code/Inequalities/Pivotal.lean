/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2


namespace StatMech

open ConfigSpace Function

variable {E : Type*} [DecidableEq E]


def setOpen (e : E) (ω : ConfigSpace E) : ConfigSpace E := Function.update ω e true


def setClosed (e : E) (ω : ConfigSpace E) : ConfigSpace E := Function.update ω e false

end StatMech
