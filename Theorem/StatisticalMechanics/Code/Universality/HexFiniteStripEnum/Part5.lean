/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part4


namespace StatMech.Universality

open Complex

open HexWalk

open scoped BigOperators


@[simp] theorem hexStrip_region_finiteRegion_mids (R : HexRegion) (M : Finset ℂ)
    (ha : R.start ∈ M) : (hexStrip_region_finiteRegion R M ha).mids = M := rfl

@[simp] theorem hexStrip_region_finiteRegion_start (R : HexRegion) (M : Finset ℂ)
    (ha : R.start ∈ M) : (hexStrip_region_finiteRegion R M ha).start = R.start := rfl

@[simp] theorem hexStrip_region_finiteRegion_verts (R : HexRegion) (M : Finset ℂ)
    (ha : R.start ∈ M) : (hexStrip_region_finiteRegion R M ha).verts = hexStrip_verts M := rfl


theorem hexStrip_single_closure (a : ℂ) (w : HexWalk)
    (hstay : ∀ m ∈ w.mids, m ∈ ({a} : Finset ℂ)) :
    ∀ x ∈ w.vertices, x ∈ hexStrip_verts ({a} : Finset ℂ) :=
  hexStrip_vertexBound ({a} : Finset ℂ) w hstay


end StatMech.Universality
