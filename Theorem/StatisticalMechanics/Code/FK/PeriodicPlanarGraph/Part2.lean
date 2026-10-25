/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part2
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


theorem PeriodicGraph.mem_orbitBox_iff (P : PeriodicGraph V) (n : ℕ) (v : V) :
    v ∈ P.orbitBox n ↔
      ∃ z : Site 2, z ∈ box 2 n ∧ ∃ u ∈ P.fundamentalDomain, P.shift z u = v := by
  simp only [PeriodicGraph.orbitBox, Finset.mem_image, Finset.mem_product,
    Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨z, u⟩, ⟨hz, hu⟩, huv⟩
    exact ⟨z, hz, u, hu, huv⟩
  · rintro ⟨z, hz, u, hu, huv⟩
    exact ⟨(z, u), ⟨hz, hu⟩, huv⟩


theorem PeriodicGraph.orbitBox_mono (P : PeriodicGraph V) : Monotone P.orbitBox := by
  intro m n hmn v hv
  rw [P.mem_orbitBox_iff] at hv ⊢
  obtain ⟨z, hz, u, hu, rfl⟩ := hv
  exact ⟨z, box_mono 2 hmn hz, u, hu, rfl⟩


theorem PeriodicGraph.mem_orbitBox_of_eventually (P : PeriodicGraph V) (v : V) :
    ∃ n, v ∈ P.orbitBox n := by
  obtain ⟨z, u, hu, rfl⟩ := P.covers v
  have hzUnion : z ∈ ⋃ n, box 2 n := by rw [iUnion_box]; trivial
  obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hzUnion
  exact ⟨n, (P.mem_orbitBox_iff n _).2 ⟨z, hz, u, hu, rfl⟩⟩


end PeriodicPlanar
end FK
end StatMech
