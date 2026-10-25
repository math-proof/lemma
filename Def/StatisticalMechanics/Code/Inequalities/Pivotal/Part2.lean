/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal


namespace StatMech

open ConfigSpace Function

variable {E : Type*} [DecidableEq E]


def IsPivotal (e : E) (A : Set (ConfigSpace E)) (ω : ConfigSpace E) : Prop :=
  (setOpen e ω ∈ A) ≠ (setClosed e ω ∈ A)


end StatMech
