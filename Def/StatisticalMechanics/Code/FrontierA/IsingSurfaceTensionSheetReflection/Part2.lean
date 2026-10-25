/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MultibondReindex
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetReflection
open Finset


namespace StatMech.FrontierA

noncomputable section

def cubicalPlaquetteZReflect {a b c : Nat} :
    CubicalPlaquette a b c -> CubicalPlaquette a b c
  | .xy i j k => .xy i j k.rev
  | .xz i j k => .xz i j k.rev
  | .yz i j k => .yz i j k.rev

def cubicalPlaquetteZReflectEquiv (a b c : Nat) :
    CubicalPlaquette a b c ≃ CubicalPlaquette a b c where
  toFun := cubicalPlaquetteZReflect
  invFun := cubicalPlaquetteZReflect
  left_inv p := by cases p <;> simp [cubicalPlaquetteZReflect]
  right_inv p := by cases p <;> simp [cubicalPlaquetteZReflect]

end
end StatMech.FrontierA
