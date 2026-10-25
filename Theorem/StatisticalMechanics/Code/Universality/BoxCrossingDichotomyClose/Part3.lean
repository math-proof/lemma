/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Def.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem bcc_dualVert_iff_reach_top (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    DualVerticalCrossing ω 0 n 0 n ↔
      ∃ y : Site 2, y ∈ topSide 0 n 0 n ∧ y ∈ bcc_dualBottomReach ω n := by
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨(y : Site 2), y.2, topSide_subset y.2, (x : Site 2), x.2, topSide_subset y.2, ?_⟩
    exact hxy
  · rintro ⟨y, hyT, _hybox, x, hxB, hyb, hconn⟩
    exact ⟨⟨x, hxB⟩, ⟨y, hyT⟩, hconn⟩


theorem bcc_bottomSide_in_dualReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {x : Site 2} (hx : x ∈ bottomSide 0 n 0 n) : x ∈ bcc_dualBottomReach ω n :=
  ⟨bottomSide_subset hx, x, hx, bottomSide_subset hx,
    connectedWithin_refl (dualConfig ω) (rect 0 n 0 n) ⟨x, bottomSide_subset hx⟩⟩


theorem bcc_dualReach_extend (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (hv : v ∈ bcc_dualBottomReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hopen : dualConfig ω s(v, w) = true) :
    w ∈ bcc_dualBottomReach ω n := by
  obtain ⟨_hvbox, x, hxB, hvbox', hconn⟩ := hv
  refine ⟨hwbox, x, hxB, hwbox, ?_⟩
  have hstep : (openSubgraphInduce 2 (dualConfig ω) (rect 0 n 0 n)).Adj ⟨v, hvbox'⟩ ⟨w, hwbox⟩ := by
    rw [openSubgraphInduce_adj]; exact ⟨hadj, hopen⟩
  exact hconn.trans hstep.reachable


theorem bcc_dualReach_boundary_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcc_dualBottomReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcc_dualBottomReach ω n) :
    dualConfig ω s(v, w) = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  exact hw (bcc_dualReach_extend ω n hv hwbox hadj h)


theorem bcc_dualReach_boundary_primal_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcc_dualBottomReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcc_dualBottomReach ω n) :
    ω (crossEdge.symm s(v, w)) = true := by
  have hcl := bcc_dualReach_boundary_closed ω n hv hwbox hadj hw
  unfold dualConfig at hcl
  simpa using hcl


theorem bcc_topSide_notin_dualReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hno : ¬ DualVerticalCrossing ω 0 n 0 n) {y : Site 2} (hy : y ∈ topSide 0 n 0 n) :
    y ∉ bcc_dualBottomReach ω n := by
  intro hyD
  exact hno ((bcc_dualVert_iff_reach_top ω n).mpr ⟨y, hy, hyD⟩)


theorem bcc_dualReach_separates (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hno : ¬ DualVerticalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ bottomSide 0 n 0 n) (hy : y ∈ topSide 0 n 0 n) :
    ¬ (latticeMinusBarrier (bcc_dualBottomReach ω n)).Reachable x y :=
  not_reachable_latticeMinusBarrier (bcc_dualBottomReach ω n)
    (bcc_bottomSide_in_dualReach ω n hx) (bcc_topSide_notin_dualReach ω n hno hy)

end Universality
end StatMech
