/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanCycleSpace
open SimpleGraph Set List Function


namespace StatMech

namespace Lattice

theorem jcs_two_components_of_region {S : Set (Site 2)} (h : jcs_JordanRegion S) :
    Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hin, hout⟩ := h
  exact jcs_two_components_of_sides S hx hy hin hout


theorem jcs_separatingSide {D B inside outside : Set (Site 2)} (S : Set (Site 2))
    (hin : ∀ z ∈ inside, z ∈ S) (hout : ∀ z ∈ outside, z ∉ S)
    (hbd : ∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v →
      u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B)) :
    jcu_HasSeparatingSide D B inside outside :=
  ⟨S, hin, hout, hbd⟩


theorem jcs_separatingSide_forces_cross {D B inside outside : Set (Site 2)} (S : Set (Site 2))
    (hinS : ∀ z ∈ inside, z ∈ S) (houtS : ∀ z ∈ outside, z ∉ S)
    (hbd : ∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v →
      u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B))
    {x y : Site 2} (hx : x ∈ inside) (hy : y ∈ outside)
    (w : (hypercubicLattice 2).Walk x y) (hwD : ∀ z ∈ w.support, z ∈ D) :
    ∃ z ∈ w.support, z ∈ B :=
  jcu_separatingSide_forces_cross (jcs_separatingSide S hinS houtS hbd) hx hy w hwD


end Lattice
end StatMech
