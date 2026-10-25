/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


def isingTorusPolarizeLowerAt (i : Fin d)
    (a : IsingDyadicTorus d k) (h : IsingDyadicTorus d k → Real) :
    IsingDyadicTorus d k → Real :=
  isingTorusTranslateField (-a)
    (isingTorusPolarizeLower i (isingTorusTranslateField a h))

def isingTorusPolarizeUpperAt (i : Fin d)
    (a : IsingDyadicTorus d k) (h : IsingDyadicTorus d k → Real) :
    IsingDyadicTorus d k → Real :=
  isingTorusTranslateField (-a)
    (isingTorusPolarizeUpper i (isingTorusTranslateField a h))

end StatMech.FrontierA
