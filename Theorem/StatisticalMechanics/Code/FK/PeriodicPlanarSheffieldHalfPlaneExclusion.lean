/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneBarrier
open MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.primalHalfPlaneBarrierReady_measureReal_eq_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    mu.real E.primalHalfPlaneBarrierReady = 1 := by
  obtain ⟨B, hB0, hB⟩ := E.exists_edgeArc_displacement_bound
  apply le_antisymm measureReal_le_one
  by_contra hnot
  have hlt : mu.real E.primalHalfPlaneBarrierReady < 1 := lt_of_not_ge hnot
  let epsilon : Real := (1 - mu.real E.primalHalfPlaneBarrierReady) / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  obtain ⟨L, U, n, hprob, hsub⟩ :=
    E.exists_highProbability_primalHalfPlaneBarrierReady
      mu hFKG hTI hunique 0 B hB0 hB hepsilon
  have hmono : mu.real (E.finiteJoinedBoundaryArmEvent 0 0 1 n L U) ≤
      mu.real E.primalHalfPlaneBarrierReady := measureReal_mono hsub
  dsimp only [epsilon] at hprob
  linarith

end StatMech.FK.PeriodicPlanar
