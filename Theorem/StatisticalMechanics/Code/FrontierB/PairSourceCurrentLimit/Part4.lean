/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxCurrentParity
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Def.StatisticalMechanics.Code.FrontierB.PairSourceCurrentLimit.Part4
open Filter MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


theorem pairSourceCurrentBoxSubsequence_strictMono
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    StrictMono (pairSourceCurrentBoxSubsequence
      d N beta hbeta x y hx hy hxy) :=
  (pairSourceCurrentLimitData d N beta hbeta x y hx hy hxy).strictMono_subsequence

theorem growingPairSourceCurrentMeasure_tendsto_infinite
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘
        pairSourceCurrentBoxSubsequence d N beta hbeta x y hx hy hxy)
      (infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) :=
  (pairSourceCurrentLimitData d N beta hbeta x y hx hy hxy).tendsto


theorem freeBoxCurrentMeasure_tendsto_along_pairSource
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      (fun k => freeBoxCurrentMeasure d
        (pairSourceCurrentBoxSubsequence d N beta hbeta x y hx hy hxy k + N)
        beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) := by
  have hcofinal : Tendsto
      (fun k => pairSourceCurrentBoxSubsequence
        d N beta hbeta x y hx hy hxy k + N) atTop atTop :=
    ((strictMono_id.add_const N).comp
      (pairSourceCurrentBoxSubsequence_strictMono
        d N beta hbeta x y hx hy hxy)).tendsto_atTop
  exact (freeBoxCurrentMeasure_tendsto_full d beta hbeta).comp hcofinal


theorem pairSourceBox_expectation_eq_freeIntegral
    (d n : ℕ) (beta : ℝ) (x y : Site d)
    (hx : x ∈ box d n) (hy : y ∈ box d n) :
    expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1)
        {pairSourceBoxSite x hx, pairSourceBoxSite y hy} =
      ∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  rw [integral_freeMeasure_spinProd d n beta 0 {x, y}
    (by simpa using Set.pair_subset hx hy), boxSpinSupport_pair hx hy]
  simpa only [boxGraph_eq_sctBoxGraph] using
    (expectationJ_one_eq_isingExpectation
      (G := StatMech.FK.boxGraph d n) beta
      {pairSourceBoxSite x hx, pairSourceBoxSite y hy})


theorem growingPairSource_expectation_tendsto
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) :
    Tendsto
      (fun k => expectationJ (StatMech.FK.boxGraph d (k + N)) beta (fun _ => 1)
        {pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx),
          pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy)})
      atTop
      (nhds (∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  have hfull := integral_freeMeasure_spinProd_tendsto_freeState_of_nonneg_field
    d beta 0 hbeta.le (le_refl 0) ({x, y} : Finset (Site d))
  have hshift := hfull.comp (tendsto_add_atTop_nat N)
  simpa only [pairSourceBox_expectation_eq_freeIntegral] using hshift

end StatMech.FrontierB
