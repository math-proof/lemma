/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part3
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

@[simp] theorem shbK4DirectPath_support
    (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E) :
    (shbK4DirectPath E h03).1.support = [(0 : Fin 4), 3] := by
  simp [shbK4DirectPath]


end StatMech.Sharpness
