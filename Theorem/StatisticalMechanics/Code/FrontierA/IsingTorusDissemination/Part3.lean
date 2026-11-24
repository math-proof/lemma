module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
public import Def.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination.Part3
open Finset
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


@[simp] theorem isingTorusCoordinateShift_apply_same
    (i : Fin d) (n : Nat) :
    isingTorusCoordinateShift (k := k) i n i = n := by
  simp [isingTorusCoordinateShift]

theorem isingTorusCoordinateShift_apply_of_ne
    (i j : Fin d) (hji : j ≠ i) (n : Nat) :
    isingTorusCoordinateShift (k := k) i n j = 0 := by
  simp [isingTorusCoordinateShift, hji]


end StatMech.FrontierA
