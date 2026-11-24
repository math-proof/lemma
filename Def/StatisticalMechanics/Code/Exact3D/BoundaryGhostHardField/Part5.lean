module
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part4
open Filter
open scoped BigOperators Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

noncomputable def boolFin2Equiv : Bool ≃ Fin 2 where
  toFun := IsingFK.bToF
  invFun := fun a => a = 0
  left_inv := by
    intro b
    cases b <;> simp [IsingFK.bToF]
  right_inv := by
    intro a
    fin_cases a <;> simp [IsingFK.bToF]


noncomputable def boolConfigFin2Equiv (V : Type*) :
    ConfigSpace V ≃ (V → Fin 2) :=
  Equiv.piCongrRight fun _ => boolFin2Equiv


end Exact3D
end StatMech
