/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedLocalized
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedIntegration
open scoped BigOperators Classical
open Finset Set
open MeasureTheory


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedIntegration

open Lattice FK RevealmentConstruction AdaptiveCovLowerGeom

open WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre

open ActiveBoundaryDifferential ActiveEdgeDifferential

open FKSharpnessWeightedPeriodic FKSharpnessWeightedStrict

open FKSharpnessWeightedLocalized

open FKSharpnessWeightedInfiniteVolume

open FKSharpnessWeightedCoherentLimit


noncomputable def weightedPhaseSum
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (q beta : Real) (n : Nat) : Real :=
  ∑ a : P, weightedPhaseProfile d phaseJ a q beta n

noncomputable def weightedPhaseSumSig
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real) (q beta : Real) : Real :=
  ∑ k ∈ Finset.range n, weightedPhaseSum d phaseJ q beta k

end FKSharpnessWeightedIntegration
end OSSS
end StatMech
