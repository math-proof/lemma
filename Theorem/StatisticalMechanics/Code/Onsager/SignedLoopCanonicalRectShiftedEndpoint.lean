/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectEndpoint
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Def.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint
open MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierB

noncomputable section

theorem ons_originPositiveBoxVertex_ne_neighbor (n : Nat) :
    ons_originPositiveBoxVertex n ≠ ons_neighborPositiveBoxVertex n := by
  intro h
  have h0 := congrFun (congrArg Subtype.val h) 0
  simp [ons_originPositiveBoxVertex, ons_neighborPositiveBoxVertex] at h0

theorem ons_originPositiveBoxVertex_adj_neighbor (n : Nat) :
    (sctBoxGraph 2 (n + 1)).Adj
      (ons_originPositiveBoxVertex n) (ons_neighborPositiveBoxVertex n) := by
  change (hypercubicLattice 2).Adj (![0, 0] : Site 2) ![1, 0]
  simp [hypercubicLattice_adj, Fin.sum_univ_two]


end
end StatMech.Onsager
