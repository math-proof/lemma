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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization.Part2
open Finset Matrix
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


noncomputable def isingTorusOrientedIndexedDartEquiv :
    ((IsingDyadicTorus d k × Fin d) × Bool) ≃
      (isingTorusGraph d k).Dart :=
  Equiv.ofBijective isingTorusOrientedIndexedDart
    isingTorusOrientedIndexedDart_bijective

noncomputable def torusDartProdEquiv :
    (isingTorusGraph d k).Dart ≃
      {p : IsingDyadicTorus d k × IsingDyadicTorus d k //
        (isingTorusGraph d k).Adj p.1 p.2} where
  toFun dart := ⟨dart.toProd, dart.adj⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv dart := by ext <;> rfl
  right_inv p := by cases p; rfl


end StatMech.FrontierA
