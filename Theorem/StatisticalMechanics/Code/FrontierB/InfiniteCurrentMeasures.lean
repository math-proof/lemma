/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentMeasures.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentPairCylinders.Part2
import Def.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
open Filter MeasureTheory


namespace StatMech.FrontierB

open Lattice

theorem infiniteCurrentBoxSubsequence_strictMono
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    StrictMono (infiniteCurrentBoxSubsequence d beta hbeta) :=
  (freePlusCurrentLimitData d beta hbeta).strictMono_subsequence

theorem freeBoxCurrentMeasure_tendsto_infiniteFree
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘
        infiniteCurrentBoxSubsequence d beta hbeta)
      (infiniteFreeCurrentMeasure d beta hbeta) :=
  (freePlusCurrentLimitData d beta hbeta).free_tendsto

theorem plusBoxCurrentMeasure_tendsto_infinitePlus
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘
        infiniteCurrentBoxSubsequence d beta hbeta)
      (infinitePlusCurrentMeasure d beta hbeta) :=
  (freePlusCurrentLimitData d beta hbeta).plus_tendsto

theorem freeBoxCurrentMeasure_cylinder_tendsto_infiniteFree
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)) :
    Tendsto
      (fun k => freeBoxCurrentMeasure d
        (infiniteCurrentBoxSubsequence d beta hbeta k) beta hbeta
        (currentCylinder S A)) atTop
      (nhds (infiniteFreeCurrentMeasure d beta hbeta
        (currentCylinder S A))) :=
  (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta).cylinder S A

theorem plusBoxCurrentMeasure_cylinder_tendsto_infinitePlus
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)) :
    Tendsto
      (fun k => plusBoxCurrentMeasure d
        (infiniteCurrentBoxSubsequence d beta hbeta k) beta hbeta
        (currentCylinder S A)) atTop
      (nhds (infinitePlusCurrentMeasure d beta hbeta
        (currentCylinder S A))) :=
  (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta).cylinder S A

end StatMech.FrontierB
