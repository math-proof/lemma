/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination.Part5
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


def isingTorusIndexedField (h : IsingDyadicTorus d k → Real)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k) :
    IsingDyadicTorus d k → Real :=
  fun x => h (g x)

def isingTorusPolarizeLowerIndexAt (i : Fin d)
    (a : IsingDyadicTorus d k)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k) :
    IsingDyadicTorus d k → IsingDyadicTorus d k :=
  fun x =>
    if isingTorusInLowerHalf i (x + -a) then
      g ((x + -a) + a)
    else
      g (isingTorusReflectSite i (x + -a) + a)

def isingTorusPolarizeUpperIndexAt (i : Fin d)
    (a : IsingDyadicTorus d k)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k) :
    IsingDyadicTorus d k → IsingDyadicTorus d k :=
  fun x =>
    if isingTorusInLowerHalf i (x + -a) then
      g (isingTorusReflectSite i (x + -a) + a)
    else
      g ((x + -a) + a)

end StatMech.FrontierA
