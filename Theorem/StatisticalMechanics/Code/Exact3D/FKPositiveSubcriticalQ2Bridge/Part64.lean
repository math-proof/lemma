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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part66
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable section

set_option maxHeartbeats 800000 in

theorem finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap_mem
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v))
    (a : {a // a ∈
      (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d}) :
    finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap Ω d a ∈
      Ω.attach.sigma
        (fun m =>
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
            m.1 d.1 d.2).attach) := by
  classical
  rcases d with ⟨v, d⟩
  rcases a with ⟨⟨w, m, p⟩, ha⟩
  change
    finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap
      Ω (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v))
      ⟨⟨w, ⟨m, p⟩⟩, ha⟩ ∈
      Ω.attach.sigma
        (fun m =>
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
            m.1 v d).attach)
  unfold finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap
  exact Finset.mem_sigma.mpr
    ⟨Finset.mem_attach _ m,
      Finset.mem_attach _
        ⟨finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice
          Ω d ha,
          finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice_mem
            Ω d ha⟩⟩

set_option maxHeartbeats 1200000 in


theorem finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap_injective
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (d : finiteBoundaryGhostTwoPointSourceData n v) :
    Function.Injective
      (finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap Ω
        (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostTwoPointSourceData n v))) := by
  classical
  intro a b hab
  rcases a with ⟨⟨w, m, p⟩, ha⟩
  rcases b with ⟨⟨w', m', p'⟩, hb⟩
  have hwv : w.1 = v := by
    simpa using
      finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_fst_eq
        Ω
        (a := (⟨w, ⟨m, p⟩⟩ :
          (finiteBoundaryGhostCutoffDecrementIndex Ω).α))
        ha
  have hw'v : w'.1 = v := by
    simpa using
      finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_fst_eq
        Ω
        (a := (⟨w', ⟨m', p'⟩⟩ :
          (finiteBoundaryGhostCutoffDecrementIndex Ω).α))
        hb
  have hw : w = w' := Subtype.ext (hwv.trans hw'v.symm)
  have hm : m = m' := by
    simpa [finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap] using
      congrArg Sigma.fst hab
  subst w'
  subst m'
  have hchoice :
      finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice Ω d ha =
        finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice Ω d hb := by
    simpa [finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap] using
      hab
  have hpval : p.1 = p'.1 := by
    calc
      p.1 =
          (finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice
            Ω d ha).1 :=
        (finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice_val
          Ω d ha).symm
      _ =
          (finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice
            Ω d hb).1 :=
        congrArg Subtype.val hchoice
      _ = p'.1 :=
        finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice_val
          Ω d hb
  have hp : p = p' := Subtype.ext hpval
  subst p'
  exact Subtype.ext rfl

set_option maxHeartbeats 1200000 in


theorem finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_localFiber_sum
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (d : finiteBoundaryGhostTwoPointSourceData n v) :
    ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
      (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v))).card ≤
      ∑ m ∈ Ω,
        (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card := by
  classical
  let D : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v) := ⟨v, d⟩
  let source := ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber D).attach
  let target :
      Finset (Sigma (fun m :
        {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
          m ∈ Ω} =>
        {p // p ∈
          finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
            m.1 v d})) :=
    Ω.attach.sigma
      (fun m =>
        (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
          m.1 v d).attach)
  have hsub :
      source.image
          (finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap Ω D) ⊆
        target := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, _ha, rfl⟩
    exact finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap_mem Ω D a
  have hcard_image :
      (source.image
          (finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap Ω D)).card =
        source.card := by
    rw [Finset.card_image_of_injective]
    exact finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap_injective
      Ω d
  have hle_target :
      ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber D).card ≤
        target.card := by
    calc
      ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber D).card =
          source.card := by
        simp [source]
      _ =
          (source.image
            (finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap
              Ω D)).card := hcard_image.symm
      _ ≤ target.card := Finset.card_le_card hsub
  have htarget_card :
      target.card =
        ∑ m ∈ Ω,
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card := by
    dsimp [target]
    rw [Finset.card_sigma]
    simpa [Finset.card_attach] using
      (Finset.sum_attach Ω
        (fun m =>
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card))
  simpa [D] using hle_target.trans_eq htarget_card

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v)) :
    ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card ≤
      ∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1) := by
  classical
  rcases d with ⟨v, d⟩
  calc
    ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
      (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v))).card ≤
        ∑ m ∈ Ω,
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card :=
      finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_localFiber_sum
        Ω d
    _ ≤ ∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v) := by
      refine Finset.sum_le_sum ?_
      intro m _hm
      simpa [finiteBoundaryGhostBoundaryEdge] using
        finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity
          m v d


theorem
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_eq_zero_of_current_ne_update_target
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    (hm :
      m ≠ Function.update d.1 (finiteBoundaryGhostBoundaryEdge n v)
        (d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1)) :
    (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  exact hm
    (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_current_eq_update_target
      m v d hp)

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCutoffDecrementIndex_localFiber_sum_le_decrementedBoundaryGhostMultiplicity_succ
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (d : finiteBoundaryGhostTwoPointSourceData n v) :
    (∑ m ∈ Ω,
      (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card) ≤
      d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 := by
  classical
  let eGhost := finiteBoundaryGhostBoundaryEdge n v
  let m0 :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ :=
    Function.update d.1 eGhost (d.1 eGhost + 1)
  have hsum_le :
      (∑ m ∈ Ω,
        (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card) ≤
        (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m0 v d).card := by
    by_cases hm0 : m0 ∈ Ω
    · calc
        (∑ m ∈ Ω,
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card) =
            (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m0 v d).card := by
          refine
            Finset.sum_eq_single
              (s := Ω)
              (f := fun m =>
                (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card)
              m0 ?_ ?_
          · intro m _hm hne
            exact
              finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_eq_zero_of_current_ne_update_target
                m v d (by
                  intro hm
                  exact hne (by simpa [m0, eGhost] using hm))
          · intro hnot
            exact False.elim (hnot hm0)
        _ ≤
            (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m0 v d).card :=
          le_rfl
    · calc
        (∑ m ∈ Ω,
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card) =
            0 := by
          exact Finset.sum_eq_zero fun m hm => by
            exact
              finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_eq_zero_of_current_ne_update_target
                m v d (by
                  intro hcur
                  exact hm0 (by simpa [m0, eGhost] using (hcur ▸ hm)))
        _ ≤
            (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m0 v d).card :=
          Nat.zero_le _
  have hlocal :
      (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m0 v d).card ≤
        d.1 eGhost + 1 :=
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_decrementedBoundaryGhostMultiplicity_succ
      m0 v d
  simpa [eGhost] using hsum_le.trans hlocal

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v)) :
    ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card ≤
      d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 := by
  classical
  rcases d with ⟨v, d⟩
  exact
    (finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_localFiber_sum
      Ω d).trans
      (finiteBoundaryGhostCutoffDecrementIndex_localFiber_sum_le_decrementedBoundaryGhostMultiplicity_succ
        Ω d)

set_option maxHeartbeats 1200000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_toSourceData_fiber_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card ≤
      ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
        (⟨d.1, d.2.toSourceData⟩ :
          Sigma (fun v : FK.boxVerts 3 n =>
            finiteBoundaryGhostTwoPointSourceData n v))).card := by
  classical
  let Ic := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let I := finiteBoundaryGhostCutoffDecrementIndex Ω
  let D : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v) :=
    ⟨d.1, d.2.toSourceData⟩
  refine
    Finset.card_le_card_of_injOn
      (fun a : Ic.α =>
        finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha Ω a)
      ?mapsTo ?inj
  · intro a ha
    have hmapc : Ic.map a = d :=
      ((FinsetFiberIndex.mem_fiber Ic d a).mp ha).2
    have hmap :
        I.map
            (finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha Ω a) =
          D := by
      have hforget :=
        finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha_map Ω a
      rw [hmapc] at hforget
      simpa [I, D] using hforget
    exact ((FinsetFiberIndex.mem_fiber I D
      (finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha Ω a)).mpr
      ⟨finiteBoundaryGhostCutoffDecrementIndex_mem_domain Ω
        (finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha Ω a),
        hmap⟩)
  · intro a _ha b _hb hab
    exact Subtype.ext hab

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card ≤
      ∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1) := by
  calc
    ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card ≤
        ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
          (⟨d.1, d.2.toSourceData⟩ :
            Sigma (fun v : FK.boxVerts 3 n =>
              finiteBoundaryGhostTwoPointSourceData n v))).card :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_toSourceData_fiber_card
        Ω d
    _ ≤ ∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1) :=
      finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum
        Ω
        (⟨d.1, d.2.toSourceData⟩ :
          Sigma (fun v : FK.boxVerts 3 n =>
            finiteBoundaryGhostTwoPointSourceData n v))

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card ≤
      d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 := by
  calc
    ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card ≤
        ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
          (⟨d.1, d.2.toSourceData⟩ :
            Sigma (fun v : FK.boxVerts 3 n =>
              finiteBoundaryGhostTwoPointSourceData n v))).card :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_toSourceData_fiber_card
        Ω d
    _ ≤ d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 :=
      finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ
        Ω
        (⟨d.1, d.2.toSourceData⟩ :
          Sigma (fun v : FK.boxVerts 3 n =>
            finiteBoundaryGhostTwoPointSourceData n v))

end


theorem finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_domain
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (a : (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).α) :
    a ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain := by
  classical
  change a ∈
    Finset.subtype
      (fun a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α =>
        a.2.1.1 ∈ finiteBoundaryGhostOnePointSourceCutoff Ω)
      (finiteBoundaryGhostCutoffDecrementIndex Ω).domain
  exact Finset.mem_subtype.mpr
    (finiteBoundaryGhostCutoffDecrementIndex_mem_domain Ω a.1)


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_card_le_crossingPairs_sum
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain.card : ℝ) ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ∑ m ∈ Ω,
          ((finiteBoundaryGhostBoundaryCrossingPairs m v).card : ℝ) := by
  classical
  let I := finiteBoundaryGhostCutoffDecrementIndex Ω
  have hsub_nat :
      (Finset.subtype
        (fun a : I.α =>
          a.2.1.1 ∈ finiteBoundaryGhostOnePointSourceCutoff Ω)
        I.domain).card ≤ I.domain.card := by
    rw [Finset.card_subtype]
    exact Finset.card_filter_le I.domain
      (fun a : I.α =>
        a.2.1.1 ∈ finiteBoundaryGhostOnePointSourceCutoff Ω)
  have hsub :
      ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain.card :
          ℝ) ≤
        ((finiteBoundaryGhostCutoffDecrementIndex Ω).domain.card : ℝ) := by
    exact_mod_cast (by
      simpa [finiteBoundaryGhostCollapsedCutoffDecrementIndex, I] using
        hsub_nat)
  calc
    ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain.card :
        ℝ) ≤
        ((finiteBoundaryGhostCutoffDecrementIndex Ω).domain.card : ℝ) :=
      hsub
    _ =
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ∑ m ∈ Ω,
            ((finiteBoundaryGhostBoundaryCrossingPairs m v).card : ℝ) :=
      finiteBoundaryGhostCutoffDecrementIndex_domain_card_eq_crossingPairs_sum
        Ω


theorem finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_image_iff
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image ↔
      ∃ a : (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).α,
        (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a = d := by
  classical
  constructor
  · intro hd
    rcases (FinsetFiberIndex.mem_image
      (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω) d).mp hd with
      ⟨a, _ha, hmap⟩
    exact ⟨a, hmap⟩
  · rintro ⟨a, hmap⟩
    exact (FinsetFiberIndex.mem_image
      (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω) d).mpr
      ⟨a, finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_domain Ω a, hmap⟩


theorem finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)}
    (hd : d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image) :
    FK.boxBoundary 3 n d.1 := by
  classical
  rcases (finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_image_iff Ω d).mp hd with
    ⟨a, hmap⟩
  have hv : FK.boxBoundary 3 n a.1.1.1 :=
    (Finset.mem_filter.mp a.1.1.2).2
  have hfst : a.1.1.1 = d.1 := by
    simpa using congrArg Sigma.fst hmap
  simpa [hfst] using hv


theorem finiteBoundaryGhostCutoffDecrementIndex_mem_image_iff
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v)) :
    d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image ↔
      ∃ a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α,
        (finiteBoundaryGhostCutoffDecrementIndex Ω).map a = d := by
  classical
  constructor
  · intro hd
    rcases (FinsetFiberIndex.mem_image
      (finiteBoundaryGhostCutoffDecrementIndex Ω) d).mp hd with
      ⟨a, _ha, hmap⟩
    exact ⟨a, hmap⟩
  · rintro ⟨a, hmap⟩
    exact (FinsetFiberIndex.mem_image
      (finiteBoundaryGhostCutoffDecrementIndex Ω) d).mpr
      ⟨a, finiteBoundaryGhostCutoffDecrementIndex_mem_domain Ω a, hmap⟩


theorem finiteBoundaryGhostCutoffDecrementIndex_image_fst_boundary
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v)}
    (hd : d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image) :
    FK.boxBoundary 3 n d.1 := by
  classical
  rcases (finiteBoundaryGhostCutoffDecrementIndex_mem_image_iff Ω d).mp hd with
    ⟨a, hmap⟩
  have hv : FK.boxBoundary 3 n a.1.1 :=
    (Finset.mem_filter.mp a.1.2).2
  have hfst : a.1.1 = d.1 := by
    simpa using congrArg Sigma.fst hmap
  simpa [hfst] using hv


theorem finiteBoundaryGhostCutoffDecrementIndex_not_mem_image_of_not_boundary
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : ¬ FK.boxBoundary 3 n v)
    (d : finiteBoundaryGhostTwoPointSourceData n v) :
    (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v)) ∉
      (finiteBoundaryGhostCutoffDecrementIndex Ω).image := by
  intro hd
  exact hv (finiteBoundaryGhostCutoffDecrementIndex_image_fst_boundary Ω hd)


theorem finiteBoundaryGhostCutoffDecrementIndex_not_mem_fiber_of_not_boundary
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : ¬ FK.boxBoundary 3 n v)
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    (a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α) :
    a ∉ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
      (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v)) := by
  intro ha
  have hfst :
      a.1.1 = v :=
    finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_fst_eq
      Ω ha
  have hvbdry : FK.boxBoundary 3 n a.1.1 :=
    (Finset.mem_filter.mp a.1.2).2
  exact hv (by simpa [hfst] using hvbdry)


theorem finiteBoundaryGhostCutoffDecrementIndex_fiber_card_eq_zero_of_not_boundary
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : ¬ FK.boxBoundary 3 n v)
    (d : finiteBoundaryGhostTwoPointSourceData n v) :
    ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
      (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro a
  exact finiteBoundaryGhostCutoffDecrementIndex_not_mem_fiber_of_not_boundary
    Ω hv d a


theorem finiteBoundaryGhostCutoffDecrementIndex_fiber_nonempty_of_mem_image
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v)}
    (hd : d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image) :
    ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).Nonempty := by
  classical
  rcases (finiteBoundaryGhostCutoffDecrementIndex_mem_image_iff Ω d).mp hd with
    ⟨a, hmap⟩
  exact ⟨a, (finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_iff_map_eq
    Ω d a).mpr hmap⟩


theorem finiteBoundaryGhostCutoffDecrementIndex_fiber_card_pos_of_mem_image
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v)}
    (hd : d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image) :
    0 < ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card :=
  Finset.card_pos.mpr
    (finiteBoundaryGhostCutoffDecrementIndex_fiber_nonempty_of_mem_image Ω hd)


theorem finiteBoundaryGhostCutoffDecrementIndex_image_sum_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤
      ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
  classical
  refine Finset.sum_nonneg ?_
  intro d _hd
  exact mul_nonneg (Nat.cast_nonneg _)
    (finiteBoundaryGhostSigmaTwoPointSourceDataWeight_nonneg hβ hH d)

theorem finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤
      ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
  classical
  refine Finset.sum_nonneg ?_
  intro d _hd
  exact mul_nonneg (Nat.cast_nonneg _)
    (finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight_nonneg hβ hH d)

set_option maxHeartbeats 800000 in


theorem finiteBoundaryGhostCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) ≤
      ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
  classical
  refine Finset.sum_le_sum ?_
  intro d _hd
  have hcard_nat :
      ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card ≤
        ∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1) :=
    finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum
      Ω d
  have hcard :
      (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) ≤
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  exact mul_le_mul_of_nonneg_right hcard
    (finiteBoundaryGhostSigmaTwoPointSourceDataWeight_nonneg hβ hH d)

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
  classical
  refine Finset.sum_le_sum ?_
  intro d _hd
  have hcard_nat :
      ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card ≤
        ∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1) :=
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum
      Ω d
  have hcard :
      (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) ≤
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  exact mul_le_mul_of_nonneg_right hcard
    (finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight_nonneg hβ hH d)

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) ≤
      ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
        (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) := by
  classical
  let I := finiteBoundaryGhostCutoffDecrementIndex Ω
  let W :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v) → ℝ :=
    finiteBoundaryGhostSigmaTwoPointSourceDataWeight
      (β := β) (H := H)
  let C :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v) → ℝ :=
    fun d =>
      ((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ)
  change
    Finset.sum I.image (fun d => ((I.fiber d).card : ℝ) * W d) ≤
      Finset.sum I.image (fun d => C d * W d)
  refine
    FinsetFiberIndex.image_sum_le_image_sum_mul_of_fiber_card_le
      I W C ?_ ?_
  · intro d _hd
    have hcard_nat :
        ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card ≤
          d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 :=
      finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ
        Ω d
    change
      (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) ≤
        (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ))
    exact_mod_cast hcard_nat
  · intro d _hd
    exact finiteBoundaryGhostSigmaTwoPointSourceDataWeight_nonneg hβ hH d

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let W :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostCollapsedTwoPointSourceData n v) → ℝ :=
    finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight
      (β := β) (H := H)
  let C :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostCollapsedTwoPointSourceData n v) → ℝ :=
    fun d =>
      ((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) :
        ℝ)
  change
    Finset.sum I.image (fun d => ((I.fiber d).card : ℝ) * W d) ≤
      Finset.sum I.image (fun d => C d * W d)
  refine
    FinsetFiberIndex.image_sum_le_image_sum_mul_of_fiber_card_le
      I W C ?_ ?_
  · intro d _hd
    have hcard_nat :
        ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card ≤
          d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ
        Ω d
    change
      (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) ≤
        (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) :
          ℝ))
    exact_mod_cast hcard_nat
  · intro d _hd
    exact finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight_nonneg
      hβ hH d

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_eq_current_weight_sum_add_weight_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d)) =
      Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d)) +
      Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).image
        (fun d => finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) := by
  classical
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d _hd
  rw [Nat.cast_add, Nat.cast_one]
  ring

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_eq_current_weight_sum_add_weight_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) =
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) +
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d => finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d _hd
  rw [Nat.cast_add, Nat.cast_one]
  ring

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_boundary_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d)) =
      Finset.sum
        (Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v))
        (fun v =>
          Finset.sum
            ((finiteBoundaryGhostCutoffDecrementIndex Ω).image.filter
              (fun d => d.1 = v))
            (fun d =>
              (((d.2.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
                finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d))) := by
  classical
  let I := finiteBoundaryGhostCutoffDecrementIndex Ω
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  let W :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v) → ℝ :=
    finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H
  let F :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v) → ℝ :=
    fun d => (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
      W d)
  have hmaps : ∀ d, d ∈ I.image → d.1 ∈ B := by
    intro d hd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        finiteBoundaryGhostCutoffDecrementIndex_image_fst_boundary Ω hd⟩
  change
    (∑ d ∈ I.image, F d) =
      ∑ v ∈ B, ∑ d ∈ I.image.filter (fun d => d.1 = v),
        (((d.2.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) * W d)
  calc
    (∑ d ∈ I.image, F d) =
        ∑ v ∈ B, ∑ d ∈ I.image.filter (fun d => d.1 = v), F d := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := I.image) (t := B) (g := fun d => d.1)
        hmaps F]
    _ =
        ∑ v ∈ B, ∑ d ∈ I.image.filter (fun d => d.1 = v),
          (((d.2.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
            W d) := by
      refine Finset.sum_congr rfl ?_
      intro v _hv
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hdv : d.1 = v := (Finset.mem_filter.mp hd).2
      simp [F, hdv]

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_boundary_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) =
      Finset.sum
        (Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v))
        (fun v =>
          Finset.sum
            ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image.filter
              (fun d => d.1 = v))
            (fun d =>
              (((d.2.toSourceData.1
                  (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
                finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d))) := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  let W :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostCollapsedTwoPointSourceData n v) → ℝ :=
    finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H
  let F :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostCollapsedTwoPointSourceData n v) → ℝ :=
    fun d =>
      (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) :
        ℝ) * W d)
  have hmaps : ∀ d, d ∈ I.image → d.1 ∈ B := by
    intro d hd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary Ω hd⟩
  change
    (∑ d ∈ I.image, F d) =
      ∑ v ∈ B, ∑ d ∈ I.image.filter (fun d => d.1 = v),
        (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) :
          ℝ) * W d)
  calc
    (∑ d ∈ I.image, F d) =
        ∑ v ∈ B, ∑ d ∈ I.image.filter (fun d => d.1 = v), F d := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := I.image) (t := B) (g := fun d => d.1)
        hmaps F]
    _ =
        ∑ v ∈ B, ∑ d ∈ I.image.filter (fun d => d.1 = v),
          (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) :
            ℝ) * W d) := by
      refine Finset.sum_congr rfl ?_
      intro v _hv
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hdv : d.1 = v := (Finset.mem_filter.mp hd).2
      simp [F, hdv]


end Exact3D
end StatMech
