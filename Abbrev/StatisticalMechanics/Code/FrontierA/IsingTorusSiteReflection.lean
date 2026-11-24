module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part3
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

abbrev IsingTorusSitePlane (i : Fin d) :=
  {x : IsingDyadicTorus d k // isingTorusOnSitePlane i x}

abbrev IsingTorusStrictLower (i : Fin d) :=
  {x : IsingDyadicTorus d k // isingTorusInStrictLower i x}


end StatMech.FrontierA
