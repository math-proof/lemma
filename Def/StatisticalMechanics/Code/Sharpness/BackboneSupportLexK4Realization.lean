/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

def shbK4Edge.code : shbK4Edge → Sym2 (Fin 4)
  | .e01 => s(0, 1)
  | .e02 => s(0, 2)
  | .e03 => s(0, 3)
  | .e12 => s(1, 2)
  | .e13 => s(1, 3)
  | .e23 => s(2, 3)

end StatMech.Sharpness
