/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
import Structure.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


namespace HexFixedBoundaryPoint

variable {V : Type*} [DecidableEq V]

variable {D : HexDomain V} {heading : V → Fin 3 → ℤ}


noncomputable def piece (Q : HexFixedBoundaryPoint D heading) :
    Finset (HexIncidence V) := {Q.incidence}


end HexFixedBoundaryPoint
end StatMech.Universality
