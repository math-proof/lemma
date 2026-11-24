module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part3


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

def ons_decKWChainLast (start : ons_Dart L) :
    List (ons_Dart L) → ons_Dart L
  | [] => start
  | target :: rest => ons_decKWChainLast target rest

end StatMech.Onsager
