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
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part8
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


theorem generalCurrentBoxSubsequence_strictMono {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    StrictMono (generalCurrentBoxSubsequence I beta hbeta) :=
  (generalInteractionCurrentLimitData I beta hbeta).strictMono_subsequence

theorem generalFreeBoxCurrentMeasure_tendsto_infinite {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    WeakCurrentConverges
      ((fun n => generalFreeBoxCurrentMeasure
        I.coupling I.nonneg n beta hbeta) ∘
          generalCurrentBoxSubsequence I beta hbeta)
      (generalInfiniteFreeCurrentMeasure I beta hbeta) :=
  (generalInteractionCurrentLimitData I beta hbeta).free_tendsto

theorem generalPlusBoxCurrentMeasure_tendsto_infinite {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    WeakCurrentConverges
      ((fun n => generalPlusBoxCurrentMeasure
        I.coupling I.nonneg n beta hbeta) ∘
          generalCurrentBoxSubsequence I beta hbeta)
      (generalInfinitePlusCurrentMeasure I beta hbeta) :=
  (generalInteractionCurrentLimitData I beta hbeta).plus_tendsto


theorem generalFreeBoxCurrentMeasure_cylinder_tendsto_infinite {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta)
    (S : Finset (Sym2 (Site d))) (A : Set (S -> Nat)) :
    Tendsto
      (fun k => generalFreeBoxCurrentMeasure I.coupling I.nonneg
        (generalCurrentBoxSubsequence I beta hbeta k) beta hbeta
          (currentCylinder S A)) atTop
      (nhds (generalInfiniteFreeCurrentMeasure I beta hbeta
        (currentCylinder S A))) :=
  (generalFreeBoxCurrentMeasure_tendsto_infinite I beta hbeta).cylinder S A


theorem generalPlusBoxCurrentMeasure_cylinder_tendsto_infinite {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta)
    (S : Finset (Sym2 (Site d))) (A : Set (S -> Nat)) :
    Tendsto
      (fun k => generalPlusBoxCurrentMeasure I.coupling I.nonneg
        (generalCurrentBoxSubsequence I beta hbeta k) beta hbeta
          (currentCylinder S A)) atTop
      (nhds (generalInfinitePlusCurrentMeasure I beta hbeta
        (currentCylinder S A))) :=
  (generalPlusBoxCurrentMeasure_tendsto_infinite I beta hbeta).cylinder S A


end StatMech.FrontierB
