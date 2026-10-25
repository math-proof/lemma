/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.alignedMarginSchedule
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalRequirement horizontalRequirement : Nat → Nat) :
    family.AlignedMarginSchedule E verticalRequirement horizontalRequirement :=
  family.exists_fullAlternatingMargins_with_requirements E
    verticalRequirement horizontalRequirement


theorem PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    ∃ (p : Nat → Real)
      (family : ∀ m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)),
      Tendsto p atTop (nhds 1) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h ↦ h.1
  let delta : Nat → Real := fun m ↦ 1 / (m + 1 : Real)
  let p : Nat → Real := fun m ↦
    (mu.real (P.orbitBoxHitsInfinite m)) ^ 2 - delta m
  have hfamily (m : Nat) : Nonempty
      (E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)) := by
    simpa only [p, delta, PeriodicGraph.setHitsInfinite_orbitBox] using
      E.exists_orbitBox_normalBoundaryBandFamily
        mu hFKG hTI hunique m (by positivity : 0 < delta m)
  let family : ∀ m,
      E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m) :=
    fun m ↦ Classical.choice (hfamily m)
  refine ⟨p, family, ?_⟩
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hdelta : Tendsto delta atTop (nhds 0) := by
    simpa only [delta] using tendsto_one_div_add_atTop_nhds_zero_nat
  convert (hhit.pow 2).sub hdelta using 1 <;> norm_num [p]


theorem PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies_with_connectorSchedule
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (radius : Nat → Nat) :
    ∃ (p : Nat → Real)
      (family : ∀ m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)),
      Tendsto p atTop (nhds 1) ∧
      ∀ m, (family m).AlignedMarginSchedule E
        (fun _ ↦ E.connectorMarginRequirement (radius m))
        (fun _ ↦ E.connectorMarginRequirement (radius m)) := by
  obtain ⟨p, family, hp⟩ :=
    E.exists_cofinalNormalBoundaryBandFamilies mu hFKG hTI hunique
  refine ⟨p, family, hp, ?_⟩
  intro m
  exact (family m).alignedMarginSchedule E
    (fun _ ↦ E.connectorMarginRequirement (radius m))
    (fun _ ↦ E.connectorMarginRequirement (radius m))


end StatMech.FK.PeriodicPlanar
