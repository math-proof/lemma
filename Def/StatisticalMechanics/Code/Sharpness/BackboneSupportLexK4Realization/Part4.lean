/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part3
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

def shbK4OddSupport (E : Finset shbK4Edge) (n : Current (Fin 4)) :
    Finset shbK4Edge :=
  E.filter fun k ↦ Odd (n k.code)

end StatMech.Sharpness
