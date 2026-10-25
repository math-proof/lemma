/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleFaces
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSingletonCuts
open Finset


namespace StatMech.Ising

noncomputable section

def fourBridgeSecondMiddleCutCounterexampleWeight
    (P : Finset (Fin 4)) : Nat :=
  match ∑ i ∈ P, 2 ^ i.val with
  | 0 => 16
  | 1 => 32
  | 2 => 1
  | 3 => 4
  | 4 => 2
  | 5 => 8
  | 6 => 1
  | 7 => 8
  | 8 => 512
  | 9 => 1024
  | 10 => 64
  | 11 => 256
  | 12 => 64
  | 13 => 256
  | 14 => 64
  | 15 => 512
  | _ => 0


end
end StatMech.Ising
