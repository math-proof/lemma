/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part2


namespace StatMech.Universality

open Complex

open HexWalk

open scoped BigOperators


@[simp] theorem hexStrip_finiteRegion_mids (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) :
    (hexStrip_finiteRegion M a ha).mids = M := rfl

@[simp] theorem hexStrip_finiteRegion_verts (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) :
    (hexStrip_finiteRegion M a ha).verts = hexStrip_verts M := rfl

@[simp] theorem hexStrip_finiteRegion_start (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) :
    (hexStrip_finiteRegion M a ha).start = a := rfl


theorem hexStrip_finiteRegion_inRegion_iff (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) (z : ℂ) :
    (hexStrip_finiteRegion M a ha).inRegion z ↔ z ∈ M := Iff.rfl


theorem hexStrip_finiteRegion_length_lt (M : Finset ℂ) (a : ℂ) (ha : a ∈ M)
    (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hstay : (ofTurns a h0 ts).StaysIn (hexStrip_finiteRegion M a ha).inRegion) :
    ts.length < (hexStrip_verts M).card := by
  have := (hexStrip_finiteRegion M a ha).length_lt a h0 ts hsaw hstay
  rwa [hexStrip_finiteRegion_verts] at this


theorem hexStrip_vertexBound_of_superset (M : Finset ℂ) (verts : Finset ℂ)
    (hsub : hexStrip_verts M ⊆ verts) (w : HexWalk)
    (hstay : ∀ m ∈ w.mids, m ∈ M) :
    ∀ x ∈ w.vertices, x ∈ verts :=
  fun x hx => hsub (hexStrip_vertexBound M w hstay x hx)


end StatMech.Universality
