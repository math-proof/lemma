/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part4
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

def isingTorusPolarizeLower (i : Fin d)
    (h : IsingDyadicTorus d k → Real) : IsingDyadicTorus d k → Real :=
  fun x => if isingTorusInLowerHalf i x then h x
    else h (isingTorusReflectSite i x)


def isingTorusPolarizeUpper (i : Fin d)
    (h : IsingDyadicTorus d k → Real) : IsingDyadicTorus d k → Real :=
  fun x => if isingTorusInLowerHalf i x
    then h (isingTorusReflectSite i x) else h x

end StatMech.FrontierA
