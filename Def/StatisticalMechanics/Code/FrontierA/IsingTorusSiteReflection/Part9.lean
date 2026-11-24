module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part9
open Finset
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

def isingTorusStrictHalfSpin (x : IsingTorusStrictLower (k := k) i)
    (sigma : ConfigSpace (IsingTorusStrictLower (k := k) i)) : Real :=
  spin sigma x

end StatMech.FrontierA
