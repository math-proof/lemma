/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part10


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem ofLocalCoordinate_support {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    (ofLocalCoordinate c hbox hdegree hrange).support =
      boundedSupportOf c.support hbox :=
  rfl


@[simp] theorem mem_ofLocalCoordinate_support {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) (x : BoundedSite d R) :
    x ∈ (ofLocalCoordinate c hbox hdegree hrange).support ↔
      x.1 ∈ c.support := by
  simpa [ofLocalCoordinate] using mem_boundedSupportOf c.support hbox x


@[simp] theorem ofLocalCoordinate_degree_val {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ((ofLocalCoordinate c hbox hdegree hrange).degree : ℕ) = c.degree :=
  rfl


@[simp] theorem ofLocalCoordinate_range_val {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ((ofLocalCoordinate c hbox hdegree hrange).range : ℕ) = c.range :=
  rfl


theorem ofLocalCoordinate_support_card {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    (ofLocalCoordinate c hbox hdegree hrange).support.card =
      c.support.carrier.card := by
  simpa [ofLocalCoordinate] using boundedSupportOf_card c.support hbox


end BoundedPolymerCase
end
end Exact3D
end StatMech
