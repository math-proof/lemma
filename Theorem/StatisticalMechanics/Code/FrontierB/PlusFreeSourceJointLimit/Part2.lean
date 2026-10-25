/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusPairSourceCurrentLimit
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Def.StatisticalMechanics.Code.FrontierB.PlusFreeSourceJointLimit.Part2
open Filter MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


theorem plusFreeSourceCurrentSubsequence_strictMono
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    StrictMono
      (plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy) :=
  (plusFreeSourceJointLimitData
    d N beta hbeta x y hx hy hxy).strictMono_subsequence

theorem growingFreePairSourceCurrentMeasure_tendsto_jointLimit
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      ((growingFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘
        plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy)
      (infiniteFreePairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy) :=
  (plusFreeSourceJointLimitData
    d N beta hbeta x y hx hy hxy).freeSource_tendsto

theorem growingPlusPairSourceCurrentMeasure_tendsto_jointLimit
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      ((growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘
        plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy)
      (infinitePlusPairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy) :=
  (plusFreeSourceJointLimitData
    d N beta hbeta x y hx hy hxy).plusSource_tendsto


theorem freeBoxCurrentMeasure_tendsto_along_plusFreeSource
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      (fun k => freeBoxCurrentMeasure d
        ((plusFreeSourceCurrentSubsequence
          d N beta hbeta x y hx hy hxy k + N) + 1) beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) := by
  have hcofinal : Tendsto
      (fun k => (plusFreeSourceCurrentSubsequence
        d N beta hbeta x y hx hy hxy k + N) + 1) atTop atTop :=
    (((strictMono_id.add_const N).add_const 1).comp
      (plusFreeSourceCurrentSubsequence_strictMono
        d N beta hbeta x y hx hy hxy)).tendsto_atTop
  exact (freeBoxCurrentMeasure_tendsto_full d beta hbeta).comp hcofinal


theorem plusBoxCurrentMeasure_tendsto_along_plusFreeSource
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      (fun k => plusBoxCurrentMeasure d
        ((plusFreeSourceCurrentSubsequence
          d N beta hbeta x y hx hy hxy k + N) + 1) beta hbeta.le)
      (infinitePlusCurrentMeasure d beta hbeta.le) := by
  have hcofinal : Tendsto
      (fun k => (plusFreeSourceCurrentSubsequence
        d N beta hbeta x y hx hy hxy k + N) + 1) atTop atTop :=
    (((strictMono_id.add_const N).add_const 1).comp
      (plusFreeSourceCurrentSubsequence_strictMono
        d N beta hbeta x y hx hy hxy)).tendsto_atTop
  exact (plusBoxCurrentMeasure_tendsto_full d beta hbeta).comp hcofinal

end StatMech.FrontierB
