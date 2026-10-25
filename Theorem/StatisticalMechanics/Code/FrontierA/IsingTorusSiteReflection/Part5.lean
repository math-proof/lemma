/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part4
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusSiteReflect_add_step_same
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusSiteReflect i (x + isingTorusStep i) =
      isingTorusSiteReflect i x - isingTorusStep i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [isingTorusSiteReflect_apply_same,
      isingTorusStep_apply_same]
    ring
  · simp [isingTorusSiteReflect_apply_of_ne i j hji,
      isingTorusStep_apply_of_ne i j hji]

theorem isingTorusSiteReflect_add_step_of_ne
    (i j : Fin d) (hji : j ≠ i) (x : IsingDyadicTorus d k) :
    isingTorusSiteReflect i (x + isingTorusStep j) =
      isingTorusSiteReflect i x + isingTorusStep j := by
  funext l
  by_cases hli : l = i
  · subst l
    have hij : i ≠ j := Ne.symm hji
    simp [isingTorusSiteReflect_apply_same,
      isingTorusStep_apply_of_ne j i hij]
  · simp [isingTorusSiteReflect_apply_of_ne i l hli]

end StatMech.FrontierA
