/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part17


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem ofLocalCoordinateAnchoredAt_degree_val
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) {a : Site d}
    (ha : a ∈ c.support)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree) (hrange : c.range ≤ maxRange) :
    ((ofLocalCoordinateAnchoredAt c ha hdiam hdegree hrange).degree : ℕ) =
      c.degree :=
  rfl

@[simp] theorem ofLocalCoordinateAnchoredAt_range_val
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) {a : Site d}
    (ha : a ∈ c.support)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree) (hrange : c.range ≤ maxRange) :
    ((ofLocalCoordinateAnchoredAt c ha hdiam hdegree hrange).range : ℕ) =
      c.range :=
  rfl


theorem toPolymerSupport_ofLocalCoordinateAnchoredAt
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) {a : Site d}
    (ha : a ∈ c.support)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree) (hrange : c.range ≤ maxRange) :
    (ofLocalCoordinateAnchoredAt c ha hdiam hdegree hrange).toPolymerSupport =
      c.support.translate (-a) := by
  rw [ofLocalCoordinateAnchoredAt, toPolymerSupport_ofLocalCoordinate]
  rfl


theorem exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree) (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
        bc.toPolymerSupport = c.support.translate v := by
  rcases hne with ⟨a, ha⟩
  refine ⟨-a, ofLocalCoordinateAnchoredAt c (a := a) (by simpa using ha)
    hdiam hdegree hrange, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact toPolymerSupport_ofLocalCoordinateAnchoredAt c (by simpa using ha)
      hdiam hdegree hrange


end BoundedPolymerCase
end
end Exact3D
end StatMech
