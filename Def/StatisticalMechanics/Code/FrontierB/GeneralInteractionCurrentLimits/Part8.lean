module
public import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Structure.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part2
open Filter MeasureTheory Set Topology
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Sharpness Lattice


noncomputable def generalInteractionCurrentLimitData {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    GeneralInteractionCurrentLimitData I beta hbeta :=
  Classical.choice (show Nonempty
      (GeneralInteractionCurrentLimitData I beta hbeta) from by
    obtain ⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩ :=
      generalFreePlusBoxCurrentMeasure_joint_subsequence
        I.coupling I.nonneg beta hbeta
    exact ⟨⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩⟩)


noncomputable def generalInfiniteFreeCurrentMeasure {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (generalInteractionCurrentLimitData I beta hbeta).freeLimit


noncomputable def generalInfinitePlusCurrentMeasure {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (generalInteractionCurrentLimitData I beta hbeta).plusLimit


noncomputable def generalCurrentBoxSubsequence {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) : Nat -> Nat :=
  (generalInteractionCurrentLimitData I beta hbeta).subsequence

end StatMech.FrontierB
