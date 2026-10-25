/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanPropIV.Part2
import Theorem.StatisticalMechanics.Code.Onsager.WindingParity


namespace StatMech.Onsager

open BigOperators


def wpar_dStraight : Fin 3 → Fin 4 := ![0, 0, 0]


def wpar_siteStraight : Fin 3 → ZMod 2 × ZMod 2 := ![((0 : ZMod 2), (0 : ZMod 2)), (1, 0), (0, 0)]


end StatMech.Onsager
