/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def isingDiagonalWalkCouplingReflectSteps
    (start : Int × Int) (level : Int) (path : List (Int × Int)) :
    List (Int × Int) :=
  match isingDiagonalWalkFirstHitSplit? start level path with
  | some split => split.reflectPrefix.steps
  | none => path.map reflectIncrement

end
end StatMech.Universality
