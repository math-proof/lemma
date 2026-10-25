/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3


namespace StatMech.Universality

open Complex

open scoped BigOperators


variable {V : Type*} [DecidableEq V]


namespace HexRegionAssign

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (A : HexRegionAssign D P R)


@[simp] theorem toFamilyData_lam : A.toFamilyData.lam = A.lam := rfl

@[simp] theorem toFamilyData_taup : A.toFamilyData.taup = A.taup := rfl

@[simp] theorem toFamilyData_taum : A.toFamilyData.taum = A.taum := rfl

@[simp] theorem toFamilyData_ups : A.toFamilyData.ups = A.ups := rfl

@[simp] theorem toFamilyData_Fa : A.toFamilyData.Fa = A.Fa := rfl

end HexRegionAssign
end StatMech.Universality
