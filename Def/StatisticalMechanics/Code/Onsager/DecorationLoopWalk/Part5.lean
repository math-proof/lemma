module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open Finset SimpleGraph

def ons_decGeometricLoopStates
    {L n : ℕ} (d : Fin n → ons_Dart L) : Fin n → ons_Dart L :=
  fun k ↦ d (-k)

end StatMech.Onsager
