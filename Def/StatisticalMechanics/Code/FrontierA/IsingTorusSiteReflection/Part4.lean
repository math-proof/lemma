/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part4
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

def isingTorusSiteSplitEquiv (i : Fin d) :
    (ConfigSpace (IsingTorusSitePlane (k := k) i) ×
      (ConfigSpace (IsingTorusStrictLower (k := k) i) ×
        ConfigSpace (IsingTorusStrictLower (k := k) i))) ≃
      ConfigSpace (IsingDyadicTorus d k) where
  toFun p := isingTorusSiteGlue i p.1 p.2.1 p.2.2
  invFun := isingTorusSiteSplit i
  left_inv p := by rcases p with ⟨boundary, lower, upper⟩; simp
  right_inv := isingTorusSiteGlue_split i


end StatMech.FrontierA
