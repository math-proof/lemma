/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part3


namespace StatMech.Universality

open Complex

open HexWalk

open scoped BigOperators


@[simp] theorem hexStrip_finiteRegion_of_superset_verts (M verts : Finset ℂ) (a : ℂ)
    (ha : a ∈ M) (hsub : hexStrip_verts M ⊆ verts) :
    (hexStrip_finiteRegion_of_superset M verts a ha hsub).verts = verts := rfl

@[simp] theorem hexStrip_finiteRegion_of_superset_mids (M verts : Finset ℂ) (a : ℂ)
    (ha : a ∈ M) (hsub : hexStrip_verts M ⊆ verts) :
    (hexStrip_finiteRegion_of_superset M verts a ha hsub).mids = M := rfl


end StatMech.Universality
