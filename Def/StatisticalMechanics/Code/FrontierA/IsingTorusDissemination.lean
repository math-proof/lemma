/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


def isingTorusTranslateField (a : IsingDyadicTorus d k)
    (u : IsingDyadicTorus d k → Real) : IsingDyadicTorus d k → Real :=
  fun x => u (x + a)


def isingTorusTranslateConfig (a : IsingDyadicTorus d k)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    ConfigSpace (IsingDyadicTorus d k) :=
  fun x => sigma (x + a)


def isingTorusTranslateConfigEquiv (a : IsingDyadicTorus d k) :
    ConfigSpace (IsingDyadicTorus d k) ≃
      ConfigSpace (IsingDyadicTorus d k) where
  toFun := isingTorusTranslateConfig a
  invFun := isingTorusTranslateConfig (-a)
  left_inv sigma := by
    funext x
    simp [isingTorusTranslateConfig, add_assoc]
  right_inv sigma := by
    funext x
    simp [isingTorusTranslateConfig, add_assoc]

end StatMech.FrontierA
