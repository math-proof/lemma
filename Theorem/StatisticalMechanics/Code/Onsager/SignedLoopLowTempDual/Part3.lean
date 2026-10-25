/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopGeometricDualWeighted
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls

noncomputable section

theorem ons_lowTempPathNumerator_eq_kwg_dual
    (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v) :
    ons_lowTempPathNumerator P.G beta path =
      (2 : Real) ^ Nat.card P.G.ConnectedComponent *
        kwg_lowTempPathDualSum P beta path := by
  let observable : Finset (kwg_Edge P) -> Real := fun F =>
    kwg_pathDefectSign P path F * Real.exp (-2 * beta) ^ F.card
  calc
    ons_lowTempPathNumerator P.G beta path =
        ∑ config : ConfigSpace P.V,
          observable (kwg_cutSet (kwg_primalEnds P) config) := by
      unfold ons_lowTempPathNumerator observable
      apply Finset.sum_congr rfl
      intro config _
      rw [kwg_pathDefectSign_cutSet, kwg_primalCut_card]
    _ = (2 : Real) ^ Nat.card P.G.ConnectedComponent *
        ∑ F : Finset (kwg_Edge P),
          if kwg_IsEven (kwg_dualEnds P) F then observable F else 0 :=
      kwg_weightedCutEvenSum P observable
    _ = _ := by rfl

theorem ons_lowTempContourDenominator_eq_kwg_dual
    (P : PlanarZ2Subgraph) (beta : Real) :
    ons_lowTempContourDenominator P.G beta =
      (2 : Real) ^ Nat.card P.G.ConnectedComponent *
        kwg_lowTempDualSum P beta := by
  let observable : Finset (kwg_Edge P) -> Real := fun F =>
    Real.exp (-2 * beta) ^ F.card
  calc
    ons_lowTempContourDenominator P.G beta =
        ∑ config : ConfigSpace P.V,
          observable (kwg_cutSet (kwg_primalEnds P) config) := by
      unfold ons_lowTempContourDenominator observable
      apply Finset.sum_congr rfl
      intro config _
      rw [kwg_primalCut_card]
    _ = (2 : Real) ^ Nat.card P.G.ConnectedComponent *
        ∑ F : Finset (kwg_Edge P),
          if kwg_IsEven (kwg_dualEnds P) F then observable F else 0 :=
      kwg_weightedCutEvenSum P observable
    _ = _ := by rfl


theorem isingExpectation_twoPoint_eq_kwg_lowTempDualRatio
    (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v) :
    isingExpectation P.G beta 0
        (fun config => spin config u * spin config v) =
      kwg_lowTempPathDualSum P beta path /
        kwg_lowTempDualSum P beta := by
  rw [isingExpectation_twoPoint_eq_lowTempPathRatio,
    ons_lowTempPathNumerator_eq_kwg_dual,
    ons_lowTempContourDenominator_eq_kwg_dual]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num : (2 : Real) ≠ 0))

end
end StatMech.Onsager
