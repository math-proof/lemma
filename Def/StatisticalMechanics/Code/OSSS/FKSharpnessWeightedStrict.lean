/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedStrict.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseClose
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedStrict

open Lattice FK RevealmentConstruction RevealmentTranslation

open WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre

open AdaptiveCovLowerGeom

open FKSharpnessWeighted FKSharpnessWeightedPeriodic

open FKSharpnessWeightedPeriodicRepair

open FKSharpnessWeightedInfiniteVolume FKSharpnessWeightedCoherentLimit


noncomputable def weightedStrictDenom
    (d n : Nat) (J : Sym2 (Site d) -> Real) (q beta : Real) : Real :=
  4 * (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
    (fun x => ∑ j ∈ Finset.range n,
      weightedOuterInnerConn d n J q beta x j) / (n : Real)


noncomputable def weightedPhaseProfile
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (q beta : Real) (k : Nat) : Real :=
  if k = 0 then 1 else weightedPhaseWiredTheta d phaseJ a q beta k


noncomputable def weightedPhaseEnvelopeSig
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real) (q beta : Real) : Real :=
  ∑ k ∈ Finset.range n,
    phaseEnvelope (fun a => weightedPhaseProfile d phaseJ a q beta) k

end FKSharpnessWeightedStrict
end OSSS
end StatMech
