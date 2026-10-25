/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part84
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_nonneg
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v := by
  exact Nat.cast_nonneg _

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_fiber_card_le_collapsedCutoff_fiber_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (d : finiteBoundaryGhostCollapsedTwoPointSourceData n v) :
    ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber
        d).card ≤
      ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber
        (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostCollapsedTwoPointSourceData n v))).card := by
  classical
  let Iloc := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
  let Iglob := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let D : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v) := ⟨v, d⟩
  refine
    Finset.card_le_card_of_injOn
      (fun a : Iloc.α =>
        finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha
          Ω hv a)
      ?mapsTo ?inj
  · intro a ha
    have hmaploc : Iloc.map a = d :=
      ((FinsetFiberIndex.mem_fiber Iloc d a).mp ha).2
    have hmapglob :
        Iglob.map
            (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha
              Ω hv a) =
          D := by
      rw [
        finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha_map,
        hmaploc]
    exact ((FinsetFiberIndex.mem_fiber Iglob D
      (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha
        Ω hv a)).mpr
      ⟨finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_domain Ω
        (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha
          Ω hv a),
        hmapglob⟩)
  · intro a _ha b _hb hab
    cases a with
    | mk ma pa =>
      cases b with
      | mk mb pb =>
        have hval :
            (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha
              Ω hv ⟨ma, pa⟩).1 =
              (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha
                Ω hv ⟨mb, pb⟩).1 :=
          congrArg Subtype.val hab
        have hmraw : ma.1 = mb.1 :=
          congrArg (fun x => x.2.1.1) hval
        have hm : ma = mb := Subtype.ext hmraw
        cases hm
        cases hval
        rfl

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (d : finiteBoundaryGhostCollapsedTwoPointSourceData n v) :
    ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber
        d).card ≤
      d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 := by
  calc
    ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber
        d).card ≤
      ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber
        (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostCollapsedTwoPointSourceData n v))).card :=
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_fiber_card_le_collapsedCutoff_fiber_card
        Ω hv d
    _ ≤ d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ
        Ω
        (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostCollapsedTwoPointSourceData n v))

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ d ∈ (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image,
        (((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber
            d).card : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ d ∈ (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image,
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) :
          ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
  let W : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
  let C : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      ((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) : ℝ)
  change
    Finset.sum I.image (fun d => ((I.fiber d).card : ℝ) * W d) ≤
      Finset.sum I.image (fun d => C d * W d)
  refine
    FinsetFiberIndex.image_sum_le_image_sum_mul_of_fiber_card_le
      I W C ?_ ?_
  · intro d _hd
    have hcard_nat :
        (I.fiber d).card ≤
          d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :=
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ
        Ω hv d
    have hcard_real :
        ((I.fiber d).card : ℝ) ≤
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
            ℕ) : ℝ)) := by
      exact_mod_cast hcard_nat
    simpa [C] using hcard_real
  · intro d _hd
    exact finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg
      hβ hH d

set_option maxHeartbeats 1200000 in
set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_fiber_card_le_localFiber_sum
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v) :
    ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      Ω v).fiber D).card ≤
      ∑ m ∈ Ω,
        (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
          m v D.2.toSourceData).card := by
  classical
  let I :=
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      Ω v
  let source := (I.fiber D).attach
  let target :
      Finset (Sigma (fun m :
        {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
          m ∈ Ω} =>
        {p // p ∈
          finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
            m.1 v D.2.toSourceData})) :=
    Ω.attach.sigma
      (fun m =>
        (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
          m.1 v D.2.toSourceData).attach)
  let f :
      {x // x ∈ I.fiber D} →
        Sigma (fun m :
          {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
            m ∈ Ω} =>
          {p // p ∈
            finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
              m.1 v D.2.toSourceData}) :=
    fun a =>
      let x := a.1
      have hmem := (FinsetFiberIndex.mem_fiber I D x).mp a.2
      have hΩ : x.1 ∈ Ω :=
        (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_mem
          Ω v x).mp hmem.1
      have htarget :
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
              n v x =
            D.2.toSourceData := by
        have hforget :=
          congrArg
            (fun E :
              finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
                n v =>
              E.2.toSourceData)
            hmem.2
        change
          (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaFullSourceClassifiedDecrementData
            n v x).toSourceData = D.2.toSourceData at hforget
        simpa using hforget
      have hp :
          x.2 ∈
            finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
              x.1 v D.2.toSourceData := by
        simpa [htarget] using
          finiteBoundaryGhostDecrementedSourceWeightVertexSigma_mem_decrementFiber
            x
      ⟨⟨x.1, hΩ⟩, ⟨x.2, hp⟩⟩
  have hsub : source.image f ⊆ target := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, _ha, rfl⟩
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_attach _ (f a).1,
        Finset.mem_attach _ (f a).2⟩
  have hinj : Function.Injective f := by
    intro a b h
    rcases a with ⟨⟨ma, pa⟩, ha⟩
    rcases b with ⟨⟨mb, pb⟩, hb⟩
    apply Subtype.ext
    have hm : ma = mb := by
      exact congrArg (fun y => y.1.1) h
    subst mb
    cases h
    rfl
  have hcard_image :
      (source.image f).card = source.card := by
    rw [Finset.card_image_of_injective]
    exact hinj
  have hle_target :
      ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
        Ω v).fiber D).card ≤ target.card := by
    calc
      ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
        Ω v).fiber D).card = source.card := by
        simp [source, I]
      _ = (source.image f).card := hcard_image.symm
      _ ≤ target.card := Finset.card_le_card hsub
  have htarget_card :
      target.card =
        ∑ m ∈ Ω,
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
            m v D.2.toSourceData).card := by
    dsimp [target]
    rw [Finset.card_sigma]
    simpa [Finset.card_attach] using
      (Finset.sum_attach Ω
        (fun m =>
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
            m v D.2.toSourceData).card))
  simpa using hle_target.trans_eq htarget_card

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v) :
    ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      Ω v).fiber D).card ≤
      D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 := by
  calc
    ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      Ω v).fiber D).card ≤
        ∑ m ∈ Ω,
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
            m v D.2.toSourceData).card :=
      finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_fiber_card_le_localFiber_sum
        Ω D
    _ ≤ D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :=
      finiteBoundaryGhostCutoffDecrementIndex_localFiber_sum_le_decrementedBoundaryGhostMultiplicity_succ
        Ω D.2.toSourceData

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ D ∈
        (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
          Ω v).image,
        (((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
          Ω v).fiber D).card : ℝ) *
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H D) ≤
      ∑ D ∈
        (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
          Ω v).image,
        (((D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) :
          ℝ) *
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H D) := by
  classical
  let I :=
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      Ω v
  let W : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ℝ :=
    finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H
  let C :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ℝ :=
    fun D =>
      ((D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) :
        ℝ)
  change
    Finset.sum I.image (fun D => ((I.fiber D).card : ℝ) * W D) ≤
      Finset.sum I.image (fun D => C D * W D)
  refine
    FinsetFiberIndex.image_sum_le_image_sum_mul_of_fiber_card_le
      I W C ?_ ?_
  · intro D _hD
    have hcard_nat :
        (I.fiber D).card ≤
          D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :=
      finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ
        Ω D
    have hcard_real :
        ((I.fiber D).card : ℝ) ≤
          (((D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
            ℕ) : ℝ)) := by
      exact_mod_cast hcard_nat
    simpa [C] using hcard_real
  · intro D _hD
    exact
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight_nonneg
        hβ hH D

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_fullSourceClassifiedVertexCurrentSupportDecrementedBoundaryGhostMultiplicity_succ_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤
      ∑ D ∈
        (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
          Ω v).image,
        (((D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) :
          ℝ) *
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H D) := by
  rw [
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum]
  exact
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum
      hβ hH Ω v

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_le_boundaryFiberCard
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image.card :
        ℝ) ≤
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v := by
  classical
  let Iloc := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
  let Iglob := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let tag :
      finiteBoundaryGhostCollapsedTwoPointSourceData n v →
        Sigma (fun w : FK.boxVerts 3 n =>
          finiteBoundaryGhostCollapsedTwoPointSourceData n w) :=
    fun d => ⟨v, d⟩
  have hmaps :
      ∀ d, d ∈ Iloc.image →
        tag d ∈ Iglob.image.filter (fun d => d.1 = v) := by
    intro d hd
    rcases (FinsetFiberIndex.mem_image Iloc d).mp hd with
      ⟨a, ha, hmap⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · refine (FinsetFiberIndex.mem_image Iglob (tag d)).mpr ?_
      let aglob :=
        finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha
          Ω hv a
      have haglob_domain : aglob ∈ Iglob.domain := by
        unfold aglob Iglob finiteBoundaryGhostCollapsedCutoffDecrementIndex
        exact
          Finset.mem_subtype.mpr
            (finiteBoundaryGhostCutoffDecrementIndex_mem_domain Ω _)
      refine ⟨aglob, haglob_domain, ?_⟩
      rw [
        finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha_map]
      simpa [tag, Iloc] using congrArg (fun x => (⟨v, x⟩ :
        Sigma (fun w : FK.boxVerts 3 n =>
          finiteBoundaryGhostCollapsedTwoPointSourceData n w))) hmap
    · rfl
  have hinj :
      ∀ d, d ∈ Iloc.image →
        ∀ d', d' ∈ Iloc.image → tag d = tag d' → d = d' := by
    intro d _hd d' _hd' hdd
    cases hdd
    rfl
  have hcard :
      Iloc.image.card ≤ (Iglob.image.filter (fun d => d.1 = v)).card :=
    Finset.card_le_card_of_injOn tag hmaps hinj
  simpa [finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard, Iloc, Iglob]
    using (show ((Iloc.image.card : ℕ) : ℝ) ≤
      (((Iglob.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) by
      exact_mod_cast hcard)


theorem finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_image_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤
      ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image.card : ℝ) := by
  classical
  unfold finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard
  exact_mod_cast
    (Finset.card_le_card
      (Finset.filter_subset (fun d => d.1 = v)
        (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image))


theorem finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_domain_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤
      ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain.card : ℝ) := by
  exact
    (finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_image_card Ω v).trans
      (FinsetFiberIndex.image_card_le_domain_card
        (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω))


end Exact3D
end StatMech
