/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedWeakLimit
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport.Part3
open MeasureTheory Set Filter Topology
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPhaseClose

open Lattice FK Percolation

open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume

open FKSharpnessWeightedCoherentLimit FKSharpnessWeightedSelectedLaws

open FKSharpnessWeightedWeakLimit FKSharpnessWeightedPhaseTransport

open FKSharpnessWeightedDomain FKSharpnessWeightedPeriodicRepair

variable {d : Nat}


noncomputable def weightedTransBoxMass
    (K : Sym2 (Site d) -> Real) (v : Site d) (N : Nat)
    (t : Finset (Sym2 (boxVerts d N))) (q beta : Real)
    (m : Nat) (hNm : N <= m) : Real :=
  med_multiMassProb
    (bcProbW (fvs_transBoxGraph d m v)
      (boundaryCliqueGraph (fvs_transBoxBoundary d m v))
      (betaParams (transBoxCoupling K m v) beta) q)
    (flc_transEdges v N t m hNm)


end FKSharpnessWeightedPhaseClose
end OSSS
end StatMech
