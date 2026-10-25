/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FiniteComplementConnected
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcExteriorClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
open Set SimpleGraph


namespace StatMech

namespace Lattice

theorem lrc_farLeft_offS {S : Set (Site 2)} {b : ℤ} (hb : ∀ q ∈ S, b ≤ q 0)
    {z : Site 2} (hz : z 0 ≤ b - 1) : z ∉ S := by
  intro hzS
  have := hb z hzS
  omega


theorem lrc_reachesFarLeft_offS {S : Set (Site 2)} (hS : arcns_OffSupportConnected S)
    {b : ℤ} (hb : ∀ q ∈ S, b ≤ q 0) {x : Site 2} (hx : x ∉ S) :
    ∃ p : (hypercubicLattice 2).Walk x ![b - 1, x 1], (∀ w ∈ p.support, w ∉ S) := by
  have hc : (![b - 1, x 1] : Site 2) ∉ S :=
    lrc_farLeft_offS hb (z := ![b - 1, x 1]) (by simp)
  exact arcns_walk_of_connected hS hx hc


end Lattice
end StatMech
