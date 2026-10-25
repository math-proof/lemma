/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

@[simp] theorem isingTorusReflectSite_apply_same
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusReflectSite i x i = isingTorusReflectCoord (x i) := by
  simp [isingTorusReflectSite]

theorem isingTorusReflectSite_apply_of_ne
    (i j : Fin d) (hji : j ≠ i) (x : IsingDyadicTorus d k) :
    isingTorusReflectSite i x j = x j := by
  simp [isingTorusReflectSite, hji]


end StatMech.FrontierA
