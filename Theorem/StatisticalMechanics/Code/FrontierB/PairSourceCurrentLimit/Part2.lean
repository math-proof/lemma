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
import Def.StatisticalMechanics.Code.FrontierB.PairSourceCurrentLimit.Part2
open Filter MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


theorem pairSourceBaseConstant_pos
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) :
    0 < pairSourceBaseConstant d N beta x y hx hy :=
  boxPairCorrelationConstant_pos d N beta hbeta _ _


theorem pairSourceBaseConstant_le_expectation
    (d N n : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (hNn : N ≤ n) :
    pairSourceBaseConstant d N beta x y hx hy ≤
      expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1)
        {pairSourceBoxSite x (box_mono d hNn hx),
          pairSourceBoxSite y (box_mono d hNn hy)} := by
  let xN := pairSourceBoxSite x hx
  let yN := pairSourceBoxSite y hy
  let xn := pairSourceBoxSite x (box_mono d hNn hx)
  let yn := pairSourceBoxSite y (box_mono d hNn hy)
  have hbase : pairSourceBaseConstant d N beta x y hx hy ≤
      expectationJ (StatMech.FK.boxGraph d N) beta (fun _ => 1) {xN, yN} :=
    boxPairCorrelationConstant_le_expectation d N beta hbeta xN yN
      (pairSourceBoxSite_ne hx hy hxy)
  calc
    pairSourceBaseConstant d N beta x y hx hy ≤
        expectationJ (StatMech.FK.boxGraph d N) beta (fun _ => 1) {xN, yN} := hbase
    _ = isingExpectation (sctBoxGraph d N) beta 0
          (spinProd (boxSpinSupport d N {x, y})) := by
      rw [boxSpinSupport_pair hx hy]
      simpa only [xN, yN, boxGraph_eq_sctBoxGraph] using
        (expectationJ_one_eq_isingExpectation
          (G := StatMech.FK.boxGraph d N) beta {xN, yN})
    _ ≤ isingExpectation (sctBoxGraph d n) beta 0
          (spinProd (boxSpinSupport d n {x, y})) :=
      isingExpectation_boxSpinSupport_mono d hNn beta hbeta.le {x, y}
        (by simpa using Set.pair_subset hx hy)
    _ = expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {xn, yn} := by
      rw [boxSpinSupport_pair (box_mono d hNn hx) (box_mono d hNn hy)]
      symm
      simpa only [xn, yn, boxGraph_eq_sctBoxGraph] using
        (expectationJ_one_eq_isingExpectation
          (G := StatMech.FK.boxGraph d n) beta {xn, yn})


end StatMech.FrontierB
