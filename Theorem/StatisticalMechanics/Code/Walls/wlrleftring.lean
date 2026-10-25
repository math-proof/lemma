/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Walls.wnbenoboundedeven
import Theorem.StatisticalMechanics.Code.Walls.wchcovering.Part3
import Theorem.StatisticalMechanics.Code.Walls.wicinterior.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem wlr_leftBoundary_off (Vc : (hypercubicLattice 2).Walk a a) {w : Site 2}
    (hw : w ∈ wic_leftBoundary Vc) : w ∉ Vc.support := hw.2.1


theorem wlr_leftBoundary_interior (Vc : (hypercubicLattice 2).Walk a a) {w : Site 2}
    (hw : w ∈ wic_leftBoundary Vc) : w ∈ jec_leftRegion Vc := hw.1


theorem wlr_leftBoundary_westSupport (Vc : (hypercubicLattice 2).Walk a a) {w : Site 2}
    (hw : w ∈ wic_leftBoundary Vc) : (![w 0 - 1, w 1] : Site 2) ∈ Vc.support := hw.2.2


theorem wlr_horizAdj_reachable (Vc : (hypercubicLattice 2).Walk a a) {c r : ℤ}
    (h0 : (![c, r] : Site 2) ∉ Vc.support) (h1 : (![c + 1, r] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![c, r] : Site 2) (![c + 1, r] : Site 2) := by
  have hadj : (hypercubicLattice 2).Adj (![c, r] : Site 2) (![c + 1, r] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ((offSupport_adj Vc _ _).mpr ⟨hadj, h0, h1⟩).reachable


theorem wlr_vertAdj_reachable (Vc : (hypercubicLattice 2).Walk a a) {c r : ℤ}
    (h0 : (![c, r] : Site 2) ∉ Vc.support) (h1 : (![c, r + 1] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![c, r] : Site 2) (![c, r + 1] : Site 2) := by
  have hadj : (hypercubicLattice 2).Adj (![c, r] : Site 2) (![c, r + 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ((offSupport_adj Vc _ _).mpr ⟨hadj, h0, h1⟩).reachable


theorem wlr_adjacent_reachable (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v) (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (offSupport Vc).Reachable u v :=
  ((offSupport_adj Vc _ _).mpr ⟨hadj, hu, hv⟩).reachable


theorem wlr_vertWall_reachable (Vc : (hypercubicLattice 2).Walk a a) (c r0 r1 : ℤ)
    (hoff : ∀ t : ℤ, t ∈ Set.uIcc r0 r1 → (![c, t] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![c, r0] : Site 2) (![c, r1] : Site 2) :=
  wnbe_vertRun_reachable Vc c r0 r1 hoff


theorem wlr_horizRun_reachable (Vc : (hypercubicLattice 2).Walk a a) (r x0 x1 : ℤ)
    (hoff : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, r] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![x0, r] : Site 2) (![x1, r] : Site 2) :=
  wnbe_horizRun_reachable Vc r x0 x1 hoff


end Lattice
end StatMech
