/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWMatrix
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part2


namespace StatMech.Onsager

def ons_turnPow (μ ν : Fin 4) : ℤ :=
  if ν = μ then 0 else if ν = μ + 1 then 1 else if ν = μ + 2 then 0 else -1


end StatMech.Onsager
