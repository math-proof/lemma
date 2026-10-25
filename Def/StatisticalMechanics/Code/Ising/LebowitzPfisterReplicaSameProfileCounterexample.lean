/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSameProfileCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.RandomCurrent


def lpReplicaSameProfileCounterEnds : Fin 5 -> Sym2 (Fin 8)
  | 0 => s(0, 2)
  | 1 => s(1, 5)
  | 2 => s(3, 7)
  | 3 => s(7, 6)
  | 4 => s(6, 4)

def lpReplicaSameProfileCounterSi : Finset (Fin 8) := {2, 3}

def lpReplicaSameProfileCounterSj : Finset (Fin 8) := {4, 5}

def lpReplicaSameProfileCounterT : Finset (Fin 8) := {0, 1}

end StatMech.Ising
