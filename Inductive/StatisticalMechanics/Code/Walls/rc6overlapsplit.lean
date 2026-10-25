/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc3_minimalwitnessencoded
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace


inductive WitnessClass where
  
  | neither : WitnessClass
  
  | onlyK : WitnessClass
  
  | onlyL : WitnessClass
  
  | both : WitnessClass
  deriving DecidableEq, Fintype, Repr

end StatMech.Walls
