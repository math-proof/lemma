/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveCounterexample
open scoped symmDiff
open Finset


namespace StatMech.Ising

namespace LPRankFiveCounterexample

def orientationBit (o : LPRankFiveCounterOrientation) (i : Fin 4) : Bool :=
  o.val.testBit i.val

def colorAt (c : LPRankFiveCounterColoring) (e : LPRankFiveCounterSlot) : Fin 4 :=
  ⟨(c.val / 4 ^ e.val) % 4, Nat.mod_lt _ (by decide)⟩


def ends (o : LPRankFiveCounterOrientation) :
    LPRankFiveCounterSlot -> Sym2 LPRankFiveCounterVertex
  | 0 => if orientationBit o 0 then s((1 : Fin 8), (7 : Fin 8))
      else s((0 : Fin 8), (6 : Fin 8))
  | 1 => if orientationBit o 1 then s((6 : Fin 8), (2 : Fin 8))
      else s((7 : Fin 8), (3 : Fin 8))
  | 2 => if orientationBit o 2 then s((3 : Fin 8), (5 : Fin 8))
      else s((2 : Fin 8), (4 : Fin 8))
  | 3 => if orientationBit o 3 then s((0 : Fin 8), (4 : Fin 8))
      else s((1 : Fin 8), (5 : Fin 8))
  | 4 => s((6 : Fin 8), (7 : Fin 8))

def colorClass (c : LPRankFiveCounterColoring) (a : Fin 4) :
    Finset LPRankFiveCounterSlot :=
  Finset.univ.filter fun e => colorAt c e = a

def rowClass (c : LPRankFiveCounterColoring) (row : Bool) :
    Finset LPRankFiveCounterSlot :=
  Finset.univ.filter fun e => if row then 2 <= colorAt c e else colorAt c e < 2

def adjacent (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot)
    (u v : LPRankFiveCounterVertex) : Prop :=
  ∃ e ∈ K, u ∈ ends o e ∧ v ∈ ends o e ∧ u ≠ v

end LPRankFiveCounterexample
end StatMech.Ising
