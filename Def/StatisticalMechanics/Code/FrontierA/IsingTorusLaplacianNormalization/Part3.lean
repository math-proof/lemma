/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusExponentialMoment
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization.Part3
open Finset Matrix
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


noncomputable def isingTorusSumLinear :
    (IsingDyadicTorus d k → Real) →ₗ[Real] Real where
  toFun f := ∑ x, f x
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' t f := by simp [Finset.mul_sum]


end StatMech.FrontierA
