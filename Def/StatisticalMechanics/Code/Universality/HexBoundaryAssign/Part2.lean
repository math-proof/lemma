/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign


namespace StatMech.Universality

open Complex

open scoped BigOperators


variable {V : Type*} [DecidableEq V]


noncomputable def hexRegionClsInc (R : HexRegion) (D : HexDomain V)
    (e : HexIncidence V) : Fin 5 :=
  hexRegionCls R (D.mid e.vtx e.edge)


end StatMech.Universality
