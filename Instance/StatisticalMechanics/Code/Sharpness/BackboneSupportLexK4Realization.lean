/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part2
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

instance (E : Finset shbK4Edge) : DecidableRel (shbK4Graph E).Adj := by
  intro x y
  simp only [shbK4Graph, SimpleGraph.fromEdgeSet_adj]
  infer_instance

end StatMech.Sharpness
