/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Def.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part2
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierB

open Ising Lattice Sharpness


theorem freeDomainSpinSupport_image {d : Nat}
    (K A : Finset (Site d)) (hA : A ⊆ K) :
    (freeDomainSpinSupport K A).image Subtype.val = A := by
  ext x
  constructor
  · rintro hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [freeDomainSpinSupport] using hy
  · intro hx
    rw [Finset.mem_image]
    exact ⟨⟨x, hA hx⟩, by simp [freeDomainSpinSupport, hx], rfl⟩


end StatMech.FrontierB
