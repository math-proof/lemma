/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWMatrix
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope


namespace StatMech.Onsager

def ons_turnZ (μ ν : Fin 4) : ZMod 4 := (ν : ZMod 4) - (μ : ZMod 4)


end StatMech.Onsager
