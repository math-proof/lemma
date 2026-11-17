/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
public import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part8
public import Theorem.StatisticalMechanics.Code.SLE.CardyCLE.Part2
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

public inductive SLEPhase where
  
  | simple : SLEPhase
  

  | selfTouching : SLEPhase
  
  | spaceFilling : SLEPhase
  deriving DecidableEq, Repr


end StatMech.SLE
