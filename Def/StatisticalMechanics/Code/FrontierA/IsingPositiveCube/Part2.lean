module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusBlockQuantitative
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingMessagerMiracleInfinite
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingPositiveCube
open Finset Set
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech Lattice

variable {d m k : Nat}


noncomputable def isingTorusPositiveCube (d m k : Nat) :
    Finset (IsingDyadicTorus d k) :=
  isingTorusImageFinset k (isingPositiveCube d m)

end StatMech.FrontierA
