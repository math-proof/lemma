/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part8
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

@[simp] theorem shbK4Path0213_support
    (E : Finset shbK4Edge) (h02 : shbK4Edge.e02 ∈ E)
    (h12 : shbK4Edge.e12 ∈ E) (h13 : shbK4Edge.e13 ∈ E) :
    (shbK4Path0213 E h02 h12 h13).1.support = [(0 : Fin 4), 2, 1, 3] := by
  simp [shbK4Path0213]

end StatMech.Sharpness
