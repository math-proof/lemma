/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part6
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem exists_alignedCrossNestedPairedSequence_with_primalAdjacent
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu)
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n))
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1)
    (padding : Nat) :
    exists data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding,
      Tendsto (fun n => max
        (mu.real (E.horizontalCrossingEvent 0
          (data.triple n).currentX 0 (data.triple n).currentY))
        (mu.real (E.verticalCrossingEvent
          (data.triple n).current.raw.data.wideLeft
          (data.triple n).current.raw.data.wideRight 0
          (data.triple n).currentY))) atTop (nhds 1) := by
  let template : Nat -> Finset V := fun n => P.orbitBox n
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  let schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0) := fun n =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
  have hslack (n : Nat) := exists_pairedAlignedConnectorSlack E Edual
    (family n) (familyDual n) (schedule n) (max (radius n) n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let slack : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n) (max (radius n) n)
      (index n) := fun n => Classical.choose_spec (hslack n)
  let triple : forall n, AlignedCrossNestedThreePairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (p n) (pDual n)
      (family n) (familyDual n) (schedule n) (index n) padding := fun n =>
    Classical.choice
      (nonempty_alignedCrossNestedThreePairedMixedBoundaryScores
        E Edual mu muDual hTI hTIDual (family n) (familyDual n)
        (schedule n) (index n) padding)
  let data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding := {
    radius := radius
    schedule := schedule
    index := index
    slack := slack
    triple := triple }
  refine ⟨data, ?_⟩
  apply hcross
      (fun n => (triple n).current.raw.data.width)
      (fun n => (triple n).current.raw.data.height)
      (fun n => (triple n).current.raw.data.width_pos)
      (fun n => (triple n).current.raw.data.height_pos)
      (fun n => (triple n).current.raw.data.base)
      (fun _ => 0) (fun n => (triple n).currentX)
      (fun _ => 0) (fun n => (triple n).currentY)
      (fun n => (triple n).current.raw.data.wideLeft)
      (fun n => (triple n).current.raw.data.wideRight)
      (fun _ => 0) (fun n => (triple n).currentY) p hp hp_le
  · intro n
    exact (triple n).current.raw.data.wideLeft_le
  · intro n
    simpa [(triple n).current.raw.narrowRight_eq] using
      (triple n).current.raw.data.narrowRight_le
  · intro n
    exact le_rfl
  · intro n
    exact le_rfl
  · intro n gridVertex vertex hvertex
    apply (triple n).current.primalConnector_subset_narrow
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (P.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex
    intro vertex hvertex
    apply (triple n).current.primalConnector_subset_narrow
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n gridVertex
    intro vertex hvertex
    rw [<- (triple n).current.raw.shortTop_eq]
    apply (triple n).current.primalConnector_subset_wide
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n i
    simpa [template, (triple n).current.raw.shortTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_bottom i)
  · intro n i
    simpa [template, (triple n).current.raw.shortTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_top i)
  · intro n j
    simpa [(triple n).current.raw.narrowRight_eq,
      (triple n).current.raw.tallTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_left j)
  · intro n j
    simpa [(triple n).current.raw.narrowRight_eq,
      (triple n).current.raw.tallTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_right j)


theorem exists_alignedCrossNestedPairedSequence_with_primalAdjacent_ge
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu)
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n))
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1)
    (padding : Nat) (lowerX lowerY : Nat -> Nat) :
    exists data : AlignedCrossNestedPairedSequence E Edual mu muDual
        p pDual family familyDual padding,
      (forall n, lowerX n <= (data.triple n).currentX) /\
      (forall n, lowerY n <= (data.triple n).currentY) /\
      (forall n, (lowerX n : Int) <=
        (data.triple n).current.raw.wideRightInt -
          (data.triple n).current.raw.wideLeftInt) /\
      Tendsto (fun n => max
        (mu.real (E.horizontalCrossingEvent 0
          (data.triple n).currentX 0 (data.triple n).currentY))
        (mu.real (E.verticalCrossingEvent
          (data.triple n).current.raw.data.wideLeft
          (data.triple n).current.raw.data.wideRight 0
          (data.triple n).currentY))) atTop (nhds 1) := by
  let template : Nat -> Finset V := fun n => P.orbitBox n
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  let schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0) := fun n =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
  have hslack (n : Nat) := exists_pairedAlignedConnectorSlack E Edual
    (family n) (familyDual n) (schedule n) (max (radius n) n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let slack : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n) (max (radius n) n)
      (index n) := fun n => Classical.choose_spec (hslack n)
  have htriple (n : Nat) :=
    exists_alignedCrossNestedThreePairedMixedBoundaryScores_ge
      E Edual mu muDual hTI hTIDual (family n) (familyDual n)
      (schedule n) (index n) padding (lowerX n) (lowerY n)
  let triple : forall n, AlignedCrossNestedThreePairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (p n) (pDual n)
      (family n) (familyDual n) (schedule n) (index n) padding := fun n =>
    Classical.choose (htriple n)
  have htripleSpec (n : Nat) := Classical.choose_spec (htriple n)
  let data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding := {
    radius := radius
    schedule := schedule
    index := index
    slack := slack
    triple := triple }
  refine ⟨data, fun n => (htripleSpec n).1,
    fun n => (htripleSpec n).2.1,
    fun n => (htripleSpec n).2.2, ?_⟩
  apply hcross
      (fun n => (triple n).current.raw.data.width)
      (fun n => (triple n).current.raw.data.height)
      (fun n => (triple n).current.raw.data.width_pos)
      (fun n => (triple n).current.raw.data.height_pos)
      (fun n => (triple n).current.raw.data.base)
      (fun _ => 0) (fun n => (triple n).currentX)
      (fun _ => 0) (fun n => (triple n).currentY)
      (fun n => (triple n).current.raw.data.wideLeft)
      (fun n => (triple n).current.raw.data.wideRight)
      (fun _ => 0) (fun n => (triple n).currentY) p hp hp_le
  · intro n
    exact (triple n).current.raw.data.wideLeft_le
  · intro n
    simpa [(triple n).current.raw.narrowRight_eq] using
      (triple n).current.raw.data.narrowRight_le
  · intro n
    exact le_rfl
  · intro n
    exact le_rfl
  · intro n gridVertex vertex hvertex
    apply (triple n).current.primalConnector_subset_narrow
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (P.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex vertex hvertex
    apply (triple n).current.primalConnector_subset_narrow
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n gridVertex vertex hvertex
    rw [<- (triple n).current.raw.shortTop_eq]
    apply (triple n).current.primalConnector_subset_wide
      (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n i
    simpa [template, (triple n).current.raw.shortTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_bottom i)
  · intro n i
    simpa [template, (triple n).current.raw.shortTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_top i)
  · intro n j
    simpa [(triple n).current.raw.narrowRight_eq,
      (triple n).current.raw.tallTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_left j)
  · intro n j
    simpa [(triple n).current.raw.narrowRight_eq,
      (triple n).current.raw.tallTop_eq] using
      le_of_lt ((triple n).current.raw.data.primal_right j)

end StatMech.FK.PeriodicPlanar
