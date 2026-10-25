/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

def encodeStep (d : Int × Int) : Bool × Bool :=
  (decide (d.1 = 1), decide (d.2 = 1))

def encodePath (path : List (Int × Int)) : List (Bool × Bool) :=
  path.map encodeStep


def horizontalRightCode (path : List (Int × Int)) : List Bool :=
  path.map (fun d => decide (d.1 = -1))

def horizontalLeftCode (path : List (Int × Int)) : List Bool :=
  path.map (fun d => decide (d.1 = 1))

def verticalCode (path : List (Int × Int)) : List Bool :=
  path.map (fun d => decide (d.2 = 1))

def lineFreeEndpoint (start : Int) : List Bool → Int
  | [] => start
  | b :: bs => lineFreeEndpoint (start + if b then 1 else -1) bs

noncomputable def intLineChoiceNext (n : Nat) (x : Int)
    (b : Bool) : Int :=
  if x = 0 ∨ x = n then x else x + if b then 1 else -1

noncomputable def intLineChoiceRun (n : Nat) : Int → List Bool → Int
  | x, [] => x
  | x, b :: bs => intLineChoiceRun n (intLineChoiceNext n x b) bs

end IsingDiagonalWalkHitSplit
end StatMech.Universality
