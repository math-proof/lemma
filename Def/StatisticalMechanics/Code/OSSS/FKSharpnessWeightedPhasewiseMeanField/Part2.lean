/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedHighBeta
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhasewiseMeanField
open scoped BigOperators
open Finset Set Filter Topology MeasureTheory


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPhasewiseMeanField

open Lattice FK Percolation

open BetaThresholdBound IntegrationSubcritical

open FKSharpnessWeightedPeriodic

open FKSharpnessWeightedInfiniteVolume

open FKSharpnessWeightedThreshold

open FKSharpnessWeightedCoherentLimit

open FKSharpnessWeightedSelectedLaws

open FKSharpnessWeightedPhaseTransport

open FKSharpnessWeightedPhaseClose


noncomputable def weightedUniformOpenConstant
    (betaOne Jmin q : Real) : Real :=
  (1 - Real.exp (-(betaOne * Jmin))) / q

end FKSharpnessWeightedPhasewiseMeanField
end OSSS
end StatMech
