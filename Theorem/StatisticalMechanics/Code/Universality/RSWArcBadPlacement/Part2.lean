/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcJordanCyclic
import Def.StatisticalMechanics.Code.Universality.RSWArcBadPlacement
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_contourArcLocalSide_iff_badEdgesOnOneArc
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hc : c.IsTrail) (hx : x ∈ c.support) (hy : y ∈ c.support) :
    RlcContourArcLocalSide G omega c hx hy ↔
      RlcContourBadEdgesOnOneArcAt G omega c hx hy := by
  classical
  have hdisjoint :=
    rlc_orderedContourArc_edges_disjoint_complementary c hc hx hy
  constructor
  · intro hside
    rcases hside with hordered | hcomplementary
    · left
      intro f g he hbad
      rcases (rlc_contourArc_edges_cover c hx hy).mp he with hord | hcomp
      · exact False.elim (hbad (hordered hord))
      · exact hcomp
    · right
      intro f g he hbad
      rcases (rlc_contourArc_edges_cover c hx hy).mp he with hord | hcomp
      · exact hord
      · exact False.elim (hbad (hcomplementary hcomp))
  · rintro (hbadComp | hbadOrd)
    · left
      intro f g he
      by_contra hbad
      have hec := rlc_orderedContourArc_edges_subset c hx hy he
      exact hdisjoint he (hbadComp hec hbad)
    · right
      intro f g he
      by_contra hbad
      have hec := rlc_complementaryContourArc_edges_subset c hx hy he
      exact hdisjoint (hbadOrd hec hbad) he


end Universality
end StatMech
