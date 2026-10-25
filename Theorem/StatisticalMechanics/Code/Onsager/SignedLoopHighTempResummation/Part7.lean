/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Def.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part7
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem rectDualPathHighTempWalkRatio_eq_finiteTwoPoint_sq
    {M N : Nat} (path : ons_RectDualPath M N)
    (beta : Real) (hbeta0 : 0 < beta) (hbetaC : beta < ons_betaC) :
    ons_rectDualPathHighTempWalkRatio path beta =
      (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0
        (fun spin ↦ StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 := by
  rw [ons_rectDualPathHighTempWalkRatio]
  have hfinite := coe_rectDualPath_finiteTwoPoint_sq_eq_bounded_walkResum
    path beta hbeta0 hbetaC
  exact hfinite.symm


theorem canonicalHighTempWalkRatio_shifted_tendsto_freeState
    (beta : Real) (hbeta0 : 0 < beta) (hbetaC : beta < ons_betaC)
    (path : ∀ n, ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)))
    (a b : Site 2)
    (hsource : ∀ᶠ n in Filter.atTop,
      ((ons_box2EquivRect (n + 1)).symm (path n).source).1 = a)
    (htarget : ∀ᶠ n in Filter.atTop,
      ((ons_box2EquivRect (n + 1)).symm (path n).target).1 = b) :
    Filter.Tendsto
      (fun n ↦ ons_rectDualPathHighTempWalkRatio (path n) beta)
      Filter.atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : MeasureTheory.Measure
          (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
  apply (ons_canonicalRectDualPathRatio_shifted_tendsto_freeState
    beta hbeta0 path a b hsource htarget).congr'
  filter_upwards with n
  calc
    ons_rectDualPathRatio
        (ons_rectDualStraightLineEmbedding
          (2 * (n + 1)) (2 * (n + 1))) (path n) beta =
        (StatMech.Ising.isingExpectation
          (ons_rectDualGraph (2 * (n + 1)) (2 * (n + 1))) beta 0
          (fun spin ↦ StatMech.Ising.spin spin (path n).source *
            StatMech.Ising.spin spin (path n).target) : Complex) ^ 2 := by
      symm
      exact coe_ons_rectDualPath_finiteTwoPoint_sq_eq_canonicalKWDet_ratio
        (path n) hbeta0
    _ = ons_rectDualPathHighTempWalkRatio (path n) beta := by
      symm
      exact rectDualPathHighTempWalkRatio_eq_finiteTwoPoint_sq
        (path n) beta hbeta0 hbetaC


theorem fixedPairHighTempWalkRatio_tendsto_freeState
    (beta : Real) (hbeta0 : 0 < beta) (hbetaC : beta < ons_betaC)
    (N : Nat) (a b : Site 2)
    (ha : a ∈ StatMech.Lattice.box 2 N)
    (hb : b ∈ StatMech.Lattice.box 2 N) (hab : a ≠ b) :
    Tendsto
      (fun n ↦ ons_rectDualPathHighTempWalkRatio
        (ons_fixedPairRectDualPath N a b ha hb hab n) beta)
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  exact canonicalHighTempWalkRatio_shifted_tendsto_freeState
    beta hbeta0 hbetaC
    (ons_fixedPairRectDualPath N a b ha hb hab) a b
    (ons_fixedPairRectDualPath_source_eventually N a b ha hb hab)
    (ons_fixedPairRectDualPath_target_eventually N a b ha hb hab)

end
end StatMech.Onsager
