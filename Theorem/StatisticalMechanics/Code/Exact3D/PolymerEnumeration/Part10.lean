/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part12


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem mem_toPolymerSupport {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) (x : Site d) :
    x ∈ c.toPolymerSupport ↔
      ∃ y, y ∈ c.support ∧ BoundedSite.val y = x := by
  classical
  change x ∈ c.support.image BoundedSite.val ↔
    ∃ y, y ∈ c.support ∧ BoundedSite.val y = x
  exact Finset.mem_image


@[simp] theorem boundedSite_val_mem_toPolymerSupport
    {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) (x : BoundedSite d R) :
    BoundedSite.val x ∈ c.toPolymerSupport ↔ x ∈ c.support := by
  constructor
  · intro hx
    rcases (mem_toPolymerSupport c (BoundedSite.val x)).mp hx with
      ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  · intro hx
    exact (mem_toPolymerSupport c (BoundedSite.val x)).mpr ⟨x, hx, rfl⟩


theorem toPolymerSupport_card {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    c.toPolymerSupport.carrier.card = c.support.card := by
  classical
  unfold toPolymerSupport
  exact Finset.card_image_of_injective c.support (by
    intro x y hxy
    exact Subtype.ext hxy)


theorem toPolymerSupport_containedInBox {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    c.toPolymerSupport.containedInBox R := by
  intro x hx
  classical
  change x ∈ c.support.image BoundedSite.val at hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  exact y.2


theorem toPolymerSupport_coordinateDiameterBound {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    c.toPolymerSupport.coordinateDiameterBound (R + R) :=
  PolymerSupport.coordinateDiameterBound_of_containedInBox
    (toPolymerSupport_containedInBox c)


theorem toPolymerSupport_ofLocalCoordinate {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    (ofLocalCoordinate c hbox hdegree hrange).toPolymerSupport = c.support := by
  ext x
  constructor
  · intro hx
    classical
    change x ∈ (boundedSupportOf c.support hbox).image BoundedSite.val at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    have hy' := (mem_boundedSupportOf c.support hbox y).mp hy
    simpa [BoundedSite.val] using hxy ▸ hy'
  · intro hx
    classical
    change x ∈ (boundedSupportOf c.support hbox).image BoundedSite.val
    refine Finset.mem_image.mpr ?_
    let y : BoundedSite d R := ⟨x, hbox x hx⟩
    refine ⟨y, ?_, rfl⟩
    exact (mem_boundedSupportOf c.support hbox y).mpr hx


@[simp] theorem mem_toPolymerSupport_ofLocalCoordinate {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) (x : Site d) :
    x ∈ (ofLocalCoordinate c hbox hdegree hrange).toPolymerSupport ↔
      x ∈ c.support := by
  rw [toPolymerSupport_ofLocalCoordinate]


theorem toPolymerSupport_ofLocalCoordinate_card {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    (ofLocalCoordinate c hbox hdegree hrange).toPolymerSupport.carrier.card =
      c.support.carrier.card := by
  rw [toPolymerSupport_ofLocalCoordinate]


end BoundedPolymerCase
end
end Exact3D
end StatMech
