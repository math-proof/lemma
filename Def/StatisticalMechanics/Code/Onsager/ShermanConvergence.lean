/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanBucketCancellation.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2


namespace StatMech.Onsager

open Matrix BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

def ons_factorMajorant (q : ℝ) (s : List E) : ℝ :=
  if s.length < 2 then 0 else q ^ (s.length - 1)

end StatMech.Onsager
