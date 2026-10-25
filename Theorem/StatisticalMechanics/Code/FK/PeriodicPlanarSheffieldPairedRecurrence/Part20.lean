/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part10
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem PeriodicPlaneEmbedding.exists_uniformOutwardBoundaryCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    exists radius,
      E.UniformOutwardBoundaryCrossingRadius mu pad radius := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_outwardBoundaryScores_crossing_max_tendsto_one
      mu hFKG hTI hunique (fun n => P.orbitBox n) hhit pad hpad
  exact ⟨radius, hcross⟩


end StatMech.FK.PeriodicPlanar
