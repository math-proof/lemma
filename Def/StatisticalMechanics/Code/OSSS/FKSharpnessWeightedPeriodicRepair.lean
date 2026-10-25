/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part5
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodicRepair
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPeriodicRepair

open Lattice FK RevealmentConstruction RevealmentTranslation

open WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre

open FKSharpnessWeightedPeriodic FKSharpnessWeightedDomain

noncomputable def weightedOuterInnerConn
    (d n : Nat) (J : Sym2 (Site d) -> Real) (q beta : Real)
    (x : Site d) (k : Nat) : Real :=
  Lindeberg.mean
    (activeBCProb (boxGraph d (2 * n))
      (wiredBoxBoundaryGraph d (2 * n))
      (betaParams (boxCoupling J (2 * n)) beta) q)
    (fun omega => if ConnectedToSet d
      (liftCfg (boxActiveEdge d n)
        (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega))
      x (centeredBoundary x k) then (1 : Real) else 0)


def WeightedPhaseOffCentreStrict (d n : Nat) {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (theta : P -> Nat -> Real) (q beta : Real) : Prop :=
  forall x, x ∈ osssBoxFinset d n -> forall k, 1 <= k -> 2 * k < n ->
    weightedOuterInnerConn d n J q beta x k <= theta (phase x) k


def PeriodicWeightedNestedDominationStrict
    (d n : Nat) {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real) (q beta : Real) : Prop :=
  PhaseCovariant J phase phaseJ ∧
    WeightedPhaseOffCentreStrict d n J phase
      (fun a => weightedPhaseWiredTheta d phaseJ a q beta) q beta


end FKSharpnessWeightedPeriodicRepair
end OSSS
end StatMech
