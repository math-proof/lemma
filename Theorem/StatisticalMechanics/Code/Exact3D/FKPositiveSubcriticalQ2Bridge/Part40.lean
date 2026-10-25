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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part41
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    (p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}) :
    p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d ↔
      finiteBoundaryGhostBoundaryCrossingPairDecrementData
        (p := p.1) m v p.2 = d := by
  classical
  letI : DecidableEq (finiteBoundaryGhostTwoPointSourceData n v) :=
    Classical.decEq _
  simp [finiteBoundaryGhostBoundaryCrossingPairDecrementFiber]


theorem finiteBoundaryGhostBoundaryCrossingPair_selectedCopy_edge
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}) :
    p.1.2.1 =
      ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩ := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let eGhost : ↥G.edgeFinset :=
    ⟨s(some v, none), by
      rw [SimpleGraph.mem_edgeFinset]
      simp [G, Sharpness.withGhost]⟩
  obtain ⟨_hKsrc, _hiK, hsome, hnone⟩ :=
    (finiteBoundaryGhostBoundaryCrossingPairs_mem m v p.1).mp p.2
  have hends :
      Sharpness.FluxEdgeCopy.endsM G m p.1.2 =
        s(some v, none) := by
    exact (Sym2.mem_and_mem_iff (by simp)).mp ⟨hsome, hnone⟩
  have hedge : p.1.2.1 = eGhost := by
    apply Subtype.ext
    simpa [Sharpness.FluxEdgeCopy.endsM, G, eGhost] using hends
  simpa [G, eGhost] using hedge


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_selectedCopy_edge
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
    (_hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d) :
    p.1.2.1 =
      ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩ :=
  finiteBoundaryGhostBoundaryCrossingPair_selectedCopy_edge m v p


set_option maxHeartbeats 800000 in


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_eq_of_selectedCopy_eq
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    {p q : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d)
    (hq : q ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d)
    (hcopy : p.1.2 = q.1.2) :
    p = q := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  rcases p with ⟨⟨Kp, ip⟩, hpdom⟩
  rcases q with ⟨⟨Kq, iq⟩, hqdom⟩
  dsimp at hcopy
  subst iq
  have hpdata :
      finiteBoundaryGhostBoundaryCrossingPairDecrementData
        (p := ⟨Kp, ip⟩) m v hpdom = d :=
    (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem
      m v d ⟨⟨Kp, ip⟩, hpdom⟩).mp hp
  have hqdata :
      finiteBoundaryGhostBoundaryCrossingPairDecrementData
        (p := ⟨Kq, ip⟩) m v hqdom = d :=
    (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem
      m v d ⟨⟨Kq, ip⟩, hqdom⟩).mp hq
  have hdata :
      finiteBoundaryGhostBoundaryCrossingPairDecrementData
        (p := ⟨Kp, ip⟩) m v hpdom =
      finiteBoundaryGhostBoundaryCrossingPairDecrementData
        (p := ⟨Kq, ip⟩) m v hqdom :=
    hpdata.trans hqdata.symm
  have hsub :
      (⟨copyDeletePreimageDecrementEraseFinset G m ip Kp,
        finiteBoundaryGhostBoundaryCrossingPairs_decremented_mem_twoPointSourceSector
          (p := ⟨Kp, ip⟩) m v hpdom⟩ :
        {K : Finset (Sharpness.FluxEdgeCopy.Copy G
            (Function.update m ip.1 (m ip.1 - 1))) //
          K ∈ finiteBoundaryGhostTwoPointSourceSector
            (Function.update m ip.1 (m ip.1 - 1)) v}) =
      ⟨copyDeletePreimageDecrementEraseFinset G m ip Kq,
        finiteBoundaryGhostBoundaryCrossingPairs_decremented_mem_twoPointSourceSector
          (p := ⟨Kq, ip⟩) m v hqdom⟩ := by
    dsimp [finiteBoundaryGhostBoundaryCrossingPairDecrementData] at hdata
    injection hdata with _ hsub
  have hdel :
      copyDeletePreimageDecrementEraseFinset G m ip Kp =
      copyDeletePreimageDecrementEraseFinset G m ip Kq := by
    exact congrArg Subtype.val hsub
  have herase : Kp.erase ip = Kq.erase ip := by
    have hmap := congrArg
      (copyDeleteEmbeddingDecrementFinset G m ip) hdel
    simpa [copyDeleteEmbeddingDecrementFinset_preimageErase] using hmap
  obtain ⟨_hKpsrc, hipKp, _hpsome, _hpnone⟩ :=
    (finiteBoundaryGhostBoundaryCrossingPairs_mem m v ⟨Kp, ip⟩).mp hpdom
  obtain ⟨_hKqsrc, hipKq, _hqsome, _hqnone⟩ :=
    (finiteBoundaryGhostBoundaryCrossingPairs_mem m v ⟨Kq, ip⟩).mp hqdom
  have hipKp' : ip ∈ Kp := by
    simpa using hipKp
  have hipKq' : ip ∈ Kq := by
    simpa using hipKq
  have hK : Kp = Kq := by
    rw [← Finset.insert_erase hipKp', ← Finset.insert_erase hipKq', herase]
  apply Subtype.ext
  cases hK
  rfl


set_option maxHeartbeats 800000 in


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v) :
    (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card ≤
      m ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩ := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let eGhost : ↥G.edgeFinset :=
    ⟨s(some v, none), by
      rw [SimpleGraph.mem_edgeFinset]
      simp [G, Sharpness.withGhost]⟩
  let ghostCopies : Finset (Sharpness.FluxEdgeCopy.Copy G m) :=
    (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)).filter
      (fun i => i.1 = eGhost)
  have hfiber_le :
      (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card ≤
        ghostCopies.card := by
    refine
      Finset.card_le_card_of_injOn
        (fun p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v} =>
          p.1.2) ?_ ?_
    · intro p hp
      change p.1.2 ∈ ghostCopies
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by
            simpa [G, eGhost] using
              finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_selectedCopy_edge
                m v d hp⟩
    · intro p hp q hq hcopy
      exact
        finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_eq_of_selectedCopy_eq
          m v d hp hq hcopy
  have hghost_le : ghostCopies.card ≤ m eGhost := by
    have hprofile :
        (ghostCopies.filter (fun i => i.1 = eGhost)).card ≤ m eGhost := by
      simpa [Sharpness.FluxEdgeCopy.profileFlux] using
        (Sharpness.FluxEdgeCopy.profileFlux_le G m ghostCopies eGhost)
    have hfilter : ghostCopies.filter (fun i => i.1 = eGhost) = ghostCopies := by
      ext i
      simp [ghostCopies]
    rw [← hfilter]
    exact hprofile
  simpa [G, eGhost] using hfiber_le.trans hghost_le


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_card
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostBoundaryCrossingPairs m v).card =
      ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
        (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card := by
  classical
  letI : DecidableEq (finiteBoundaryGhostTwoPointSourceData n v) :=
    Classical.decEq _
  have h :=
    Finset.card_eq_sum_card_image
      (fun p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v} =>
        finiteBoundaryGhostBoundaryCrossingPairDecrementData
          (p := p.1) m v p.2)
      (finiteBoundaryGhostBoundaryCrossingPairs m v).attach
  simpa [finiteBoundaryGhostBoundaryCrossingPairDecrementImage,
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber, Finset.card_attach]
    using h


theorem finset_sum_attach_image_fiber_weight_nsmul
    {α β M : Type*} [DecidableEq β] [AddCommMonoid M]
    (S : Finset α) (f : {x // x ∈ S} → β) (W : β → M) :
    (∑ x ∈ S.attach, W (f x)) =
      ∑ y ∈ S.attach.image f,
        (S.attach.filter (fun x => f x = y)).card • W y := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := S.attach) (t := S.attach.image f) (g := f)
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (fun x => W (f x))]
  refine Finset.sum_congr rfl ?_
  intro y _hy
  have hinner :
      (∑ x ∈ S.attach.filter (fun x => f x = y), W (f x)) =
        ∑ _x ∈ S.attach.filter (fun x => f x = y), W y := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact congrArg W (Finset.mem_filter.mp hx).2
  rw [hinner, Finset.sum_const]


theorem finset_sum_image_fiber_card_mul
    {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (W : β → ℝ) :
    Finset.sum S (fun x => W (f x)) =
      Finset.sum (S.image f)
        (fun y => ((S.filter (fun x => f x = y)).card : ℝ) * W y) := by
  classical
  calc
    Finset.sum S (fun x => W (f x)) =
        Finset.sum S
          (fun x => Finset.sum (S.image f)
            (fun y => if f x = y then W y else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hfx : f x ∈ S.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      rw [Finset.sum_eq_single (f x)]
      · simp
      · intro y _hy hne
        simp [hne.symm]
      · intro hnot
        exact (hnot hfx).elim
    _ =
        Finset.sum (S.image f)
          (fun y => Finset.sum S (fun x => if f x = y then W y else 0)) := by
      rw [Finset.sum_comm]
    _ =
        Finset.sum (S.image f)
          (fun y => ((S.filter (fun x => f x = y)).card : ℝ) * W y) := by
      refine Finset.sum_congr rfl ?_
      intro y _hy
      rw [← Finset.sum_filter]
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]


theorem finset_sum_mul_le_const_mul_sum_of_le_nonneg
    {α : Type*} (S : Finset α) (C W : α → ℝ) {M : ℝ}
    (hC : ∀ x, x ∈ S → C x ≤ M)
    (hW : ∀ x, x ∈ S → 0 ≤ W x) :
    (∑ x ∈ S, C x * W x) ≤ M * ∑ x ∈ S, W x := by
  calc
    (∑ x ∈ S, C x * W x) ≤ ∑ x ∈ S, M * W x := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact mul_le_mul_of_nonneg_right (hC x hx) (hW x hx)
    _ = M * ∑ x ∈ S, W x := by
      rw [← Finset.mul_sum]


theorem finset_sum_le_subtype_sum_of_inactive_nonpos
    {α : Type*}
    (S : Finset α) (p : α → Prop) [DecidablePred p]
    (F : α → ℝ) (G : {a // p a} → ℝ)
    (hnot : ∀ a, a ∈ S → ¬ p a → F a ≤ 0)
    (hle : ∀ a, a ∈ S → (ha : p a) → F a ≤ G ⟨a, ha⟩) :
    Finset.sum S F ≤ Finset.sum (Finset.subtype p S) G := by
  classical
  let A : α → ℝ := fun a => if h : p a then G ⟨a, h⟩ else 0
  have hpoint : ∀ a ∈ S, F a ≤ A a := by
    intro a ha
    by_cases hpa : p a
    · simpa [A, hpa] using hle a ha hpa
    · simpa [A, hpa] using hnot a ha hpa
  have hfilter :
      Finset.sum S A = Finset.sum (S.filter p) A := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro a _ha
    by_cases hpa : p a <;> simp [A, hpa]
  have hfilter_subtype :
      Finset.sum (S.filter p) A = Finset.sum (Finset.subtype p S) G := by
    symm
    refine Finset.sum_bij
      (fun a _ha => a.1)
      ?_ ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_subtype.mp ha, a.2⟩
    · intro a _ha b _hb hab
      exact Subtype.ext hab
    · intro b hb
      exact
        ⟨⟨b, (Finset.mem_filter.mp hb).2⟩,
          Finset.mem_subtype.mpr (Finset.mem_filter.mp hb).1, rfl⟩
    · intro a _ha
      have hpa : p a.1 := a.2
      simp [hpa]
  calc
    Finset.sum S F ≤ Finset.sum S A :=
      Finset.sum_le_sum hpoint
    _ = Finset.sum (Finset.subtype p S) G := by
      rw [hfilter, hfilter_subtype]


end Exact3D
end StatMech
