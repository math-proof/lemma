/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeighted
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxLocalized.Part3
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxOffCentre.Part4
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic
open scoped BigOperators Classical
open Finset Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPeriodic

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open WiredBoxDifferential FK RevealmentTranslation

open FKSharpnessWeighted

open ActiveBoundaryDifferential ActiveEdgeDifferential LindebergTree


noncomputable def phaseEnvelope {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Nat -> Real) (n : Nat) : Real :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => theta a n)


noncomputable def weightedPhaseWiredTheta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (q beta : Real) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (boxGraph d (2 * k))
      (wiredBoxBoundaryGraph d (2 * k))
      (FK.betaParams (phaseBoxCoupling phaseJ a (2 * k)) beta) q)
    (WiredBoxLocalized.innerCrossInd d k)

end FKSharpnessWeightedPeriodic
end OSSS
end StatMech
