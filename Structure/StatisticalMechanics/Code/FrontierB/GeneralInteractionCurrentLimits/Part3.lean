/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part6
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


structure GeneralInteractionCurrentSubsequencePackage {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) : Prop where
  subsequence_strict : StrictMono (generalCurrentBoxSubsequence I beta hbeta)
  free_weak : WeakCurrentConverges
    ((fun n => generalFreeBoxCurrentMeasure
      I.coupling I.nonneg n beta hbeta) ∘
        generalCurrentBoxSubsequence I beta hbeta)
    (generalInfiniteFreeCurrentMeasure I beta hbeta)
  plus_weak : WeakCurrentConverges
    ((fun n => generalPlusBoxCurrentMeasure
      I.coupling I.nonneg n beta hbeta) ∘
        generalCurrentBoxSubsequence I beta hbeta)
    (generalInfinitePlusCurrentMeasure I beta hbeta)
  free_cylinder : forall (S : Finset (Sym2 (Site d))) (A : Set (S -> Nat)),
    Tendsto
      (fun k => generalFreeBoxCurrentMeasure I.coupling I.nonneg
        (generalCurrentBoxSubsequence I beta hbeta k) beta hbeta
          (currentCylinder S A)) atTop
      (nhds (generalInfiniteFreeCurrentMeasure I beta hbeta
        (currentCylinder S A)))
  plus_cylinder : forall (S : Finset (Sym2 (Site d))) (A : Set (S -> Nat)),
    Tendsto
      (fun k => generalPlusBoxCurrentMeasure I.coupling I.nonneg
        (generalCurrentBoxSubsequence I beta hbeta k) beta hbeta
          (currentCylinder S A)) atTop
      (nhds (generalInfinitePlusCurrentMeasure I beta hbeta
        (currentCylinder S A)))

end StatMech.FrontierB
