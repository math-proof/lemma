/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MultibondReindex
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
open Finset


namespace StatMech.FrontierA

noncomputable section

def cubicalCellZReflect {a b c : Nat} (q : CubicalCell a b c) :
    CubicalCell a b c :=
  ⟨q.x, q.y, q.z.rev⟩

def cubicalCellZReflectEquiv (a b c : Nat) :
    CubicalCell a b c ≃ CubicalCell a b c where
  toFun := cubicalCellZReflect
  invFun := cubicalCellZReflect
  left_inv q := by cases q; simp [cubicalCellZReflect]
  right_inv q := by cases q; simp [cubicalCellZReflect]


def cubicalDualVertexZReflectEquiv (a b c : Nat) :
    CubicalDualVertex a b c ≃ CubicalDualVertex a b c :=
  Equiv.optionCongr (cubicalCellZReflectEquiv a b c)

end
end StatMech.FrontierA
