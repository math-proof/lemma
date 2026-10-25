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
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPeriodic

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open WiredBoxDifferential FK RevealmentTranslation

open FKSharpnessWeighted

open ActiveBoundaryDifferential ActiveEdgeDifferential LindebergTree


theorem weightedPhaseWiredTheta_nonneg
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (a : P) (q beta : Real) (hq : 0 < q) (hbeta : 0 < beta)
    (k : Nat) :
    0 <= weightedPhaseWiredTheta d phaseJ a q beta k := by
  unfold weightedPhaseWiredTheta Lindeberg.mean
  apply Finset.sum_nonneg
  intro omega homega
  apply mul_nonneg
  · unfold WiredBoxLocalized.innerCrossInd crossIndG
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  · exact (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun e => hJ a (Sym2.map Subtype.val e)) hbeta)
      (FK.betaParams_lt_one _ beta) hq omega).le

theorem le_phaseEnvelope {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Nat -> Real) (a : P) (n : Nat) :
    theta a n <= phaseEnvelope theta n := by
  exact Finset.le_sup' (fun b => theta b n) (Finset.mem_univ a)

theorem phaseEnvelope_nonneg {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Nat -> Real) (htheta : forall a n, 0 <= theta a n)
    (n : Nat) : 0 <= phaseEnvelope theta n := by
  obtain ⟨a⟩ := (inferInstance : Nonempty P)
  exact (htheta a n).trans (le_phaseEnvelope theta a n)


end FKSharpnessWeightedPeriodic
end OSSS
end StatMech
