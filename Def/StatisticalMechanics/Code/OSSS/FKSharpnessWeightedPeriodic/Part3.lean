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
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPeriodic

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open WiredBoxDifferential FK RevealmentTranslation

open FKSharpnessWeighted

open ActiveBoundaryDifferential ActiveEdgeDifferential LindebergTree


def WeightedPhaseOffCentre (d n : Nat) {P : Type*}
    (J : Sym2 (boxVerts d n) -> Real) (phase : Site d -> P)
    (theta : P -> Nat -> Real) (q beta : Real) : Prop :=
  forall x, x ∈ osssBoxFinset d n -> forall k, k ∈ Finset.range n ->
    Lindeberg.mean
        (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
          (FK.betaParams J beta) q)
        (fun omega => if ConnectedToSet d
          (liftCfg (boxActiveEdge d n) omega) x (centeredBoundary x k)
          then (1 : Real) else 0) <=
      theta (phase x) k


def PeriodicWeightedNestedDomination
    (d n : Nat) {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real) (q beta : Real) : Prop :=
  PhaseCovariant J phase phaseJ ∧
    WeightedPhaseOffCentre d n (boxCoupling J n) phase
      (fun a => weightedPhaseWiredTheta d phaseJ a q beta) q beta


noncomputable def weightedPhaseDenom {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Nat -> Real) (n : Nat) : Real :=
  4 * (∑ k ∈ Finset.range n, phaseEnvelope theta k) / (n : Real)


end FKSharpnessWeightedPeriodic
end OSSS
end StatMech
