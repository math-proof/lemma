/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


def isingTorusHalfSpin (x : IsingTorusLowerSite (k := k) i)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) : Real :=
  spin sigma x

end StatMech.FrontierA
