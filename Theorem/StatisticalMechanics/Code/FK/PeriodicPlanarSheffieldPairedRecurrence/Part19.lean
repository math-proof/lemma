/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part9
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem PeriodicPlaneEmbedding.exists_uniformAdjacentBoundaryBandRadius_with_cofinalConnectorSchedule
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    exists (radius : Nat -> Nat) (p : Nat -> Real)
      (family : forall m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)),
      E.UniformAdjacentBoundaryBandCrossingRadius mu step radius /\
      Tendsto p atTop (nhds 1) /\
      forall m, (family m).AlignedMarginSchedule E
        (fun _ => E.connectorMarginRequirement (radius m))
        (fun _ => E.connectorMarginRequirement (radius m)) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hradius⟩ :=
    E.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius
      mu hFKG hTI hunique (fun n => P.orbitBox n) hhit step hstep
  obtain ⟨p, family, hp, hschedule⟩ :=
    E.exists_cofinalNormalBoundaryBandFamilies_with_connectorSchedule
      mu hFKG hTI hunique radius
  exact ⟨radius, p, family, hradius, hp, hschedule⟩


end StatMech.FK.PeriodicPlanar
