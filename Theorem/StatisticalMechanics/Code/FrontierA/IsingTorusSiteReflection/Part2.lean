/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

@[simp] theorem isingTorusSiteReflect_apply_same
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusSiteReflect i x i = -x i := by
  simp [isingTorusSiteReflect]

theorem isingTorusSiteReflect_apply_of_ne
    (i j : Fin d) (hji : j ≠ i) (x : IsingDyadicTorus d k) :
    isingTorusSiteReflect i x j = x j := by
  simp [isingTorusSiteReflect, hji]

@[simp] theorem isingTorusSiteReflect_involutive
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusSiteReflect i (isingTorusSiteReflect i x) = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [isingTorusSiteReflect_apply_of_ne i j hji]


end StatMech.FrontierA
