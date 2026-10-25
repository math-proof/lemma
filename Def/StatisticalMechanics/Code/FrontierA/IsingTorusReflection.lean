/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

def isingTorusReflectCoord (z : ZMod (2 ^ (k + 2))) :
    ZMod (2 ^ (k + 2)) :=
  ((2 ^ (k + 2) - 1 - z.val : Nat) : ZMod (2 ^ (k + 2)))

end StatMech.FrontierA
