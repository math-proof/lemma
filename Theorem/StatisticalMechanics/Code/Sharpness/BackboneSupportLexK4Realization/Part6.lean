/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part6
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

@[simp] theorem shbK4Path0123_support
    (E : Finset shbK4Edge) (h01 : shbK4Edge.e01 ∈ E)
    (h12 : shbK4Edge.e12 ∈ E) (h23 : shbK4Edge.e23 ∈ E) :
    (shbK4Path0123 E h01 h12 h23).1.support = [(0 : Fin 4), 1, 2, 3] := by
  simp [shbK4Path0123]

end StatMech.Sharpness
