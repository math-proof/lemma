module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.QuadraticDiscriminant
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection
open Finset
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


def isingTorusHalfSpin (x : IsingTorusLowerSite (k := k) i)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) : Real :=
  spin sigma x

end StatMech.FrontierA
