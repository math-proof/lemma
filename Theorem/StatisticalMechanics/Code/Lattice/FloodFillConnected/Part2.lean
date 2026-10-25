/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Def.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem ffc_reachable_iff_offSupportWalk {B : Set (Site 2)} {x y : Site 2} (hx : x ∉ B) :
    (ffc_offSupportLattice B).Reachable x y ↔
      ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B := by
  constructor
  · rintro ⟨w⟩
    obtain ⟨p, hp, _⟩ := ffc_project_walk w hx
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨ffc_lift_walk p hp⟩


end Lattice
end StatMech
