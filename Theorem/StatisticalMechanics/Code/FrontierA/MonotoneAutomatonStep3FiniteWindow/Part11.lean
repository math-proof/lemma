/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part10
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem measurableSet_step3CoreWindowEvent (T : MonotoneAutomaton d)
    (D N K : ℕ) : MeasurableSet (step3CoreWindowEvent T D N K) := by
  have hfirst := (measurable_interpolatedHighPair T)
    (measurableSet_pairStep3DistanceAt 0 D)
  have hmult : Measurable (fun q : FieldTriple d =>
      finiteEventMultiplicity
        ((boxFinsetBK d N).product (boxFinsetBK d N))
        (step3ContactEvent T D) q) :=
    measurable_finiteEventMultiplicity_countable _ _
      (fun p _ => measurableSet_step3ContactEvent T D p)
  have heq : (fun q : FieldTriple d => (step3WindowContacts T D N q).card) =
      finiteEventMultiplicity
        ((boxFinsetBK d N).product (boxFinsetBK d N))
        (step3ContactEvent T D) := by
    funext q
    classical
    rfl
  rw [step3CoreWindowEvent]
  apply hfirst.inter
  have hset : {q : FieldTriple d | K ≤ (step3WindowContacts T D N q).card} =
      {q | K ≤ finiteEventMultiplicity
        ((boxFinsetBK d N).product (boxFinsetBK d N))
        (step3ContactEvent T D) q} := by
    ext q
    exact (congrArg (fun f => K ≤ f q) heq).to_iff
  rw [hset]
  exact hmult measurableSet_Ici

theorem boxFinsetBK_mono {N M : ℕ} (hNM : N ≤ M) :
    boxFinsetBK d N ⊆ boxFinsetBK d M := by
  intro x hx
  rw [mem_boxFinsetBK_iff] at hx ⊢
  exact box_mono d hNM hx

theorem step3WindowContacts_card_mono (T : MonotoneAutomaton d)
    (D : ℕ) {N M : ℕ} (hNM : N ≤ M) (q : FieldTriple d) :
    (step3WindowContacts T D N q).card ≤
      (step3WindowContacts T D M q).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  change p ∈ step3WindowContacts T D N q at hp
  have hpMem : p ∈ ((boxFinsetBK d N).product
      (boxFinsetBK d N)).filter
        (fun p => q ∈ step3ContactEvent T D p) := by
    simpa [step3WindowContacts] using hp
  have hp' := Finset.mem_filter.mp hpMem
  have hpBox := Finset.mem_product.mp hp'.1
  rw [step3WindowContacts, Finset.mem_filter]
  exact ⟨Finset.mem_product.mpr
    ⟨boxFinsetBK_mono hNM hpBox.1, boxFinsetBK_mono hNM hpBox.2⟩, hp'.2⟩

theorem step3CoreWindowEvent_mono (T : MonotoneAutomaton d) (D K : ℕ) :
    Monotone (fun N => step3CoreWindowEvent T D N K) := by
  intro N M hNM q hq
  exact ⟨hq.1, hq.2.trans (step3WindowContacts_card_mono T D hNM q)⟩

theorem exists_low_contact_distance_of_mem_nearest
    {omega : PairSiteConfig d} {root y : Site d} {D : ℕ}
    (hD : omega ∈ pairStep3DistanceAt root D)
    (hy : y ∈ pairNearestHighSet omega root) :
    ∃ x ∈ pairLowInfiniteVertices omega, l1dist d x y = D := by
  rcases hy with ⟨hyCluster, x, hxLow, hxy⟩
  rcases hD.2 with ⟨z, hzCluster, a, haLow, hza⟩
  have hsetLe : setL1Distance (pairHighCluster omega root)
      (pairLowInfiniteVertices omega) ≤ D := by
    rw [← hza]
    exact Nat.sInf_le ⟨z, hzCluster, a, haLow, rfl⟩
  have hDLe : D ≤ setL1Distance (pairHighCluster omega root)
      (pairLowInfiniteVertices omega) := by
    rw [← hxy]
    exact hD.1.2 y hyCluster x hxLow
  refine ⟨x, hxLow, ?_⟩
  rw [l1dist_comm, hxy, le_antisymm hsetLe hDLe]

theorem step3Distance_preimage_eq_iUnion_windows
    (T : MonotoneAutomaton d) (D K : ℕ) :
    (interpolatedHighPair T) ⁻¹' pairStep3DistanceAt (0 : Site d) D =
      ⋃ N : ℕ, step3CoreWindowEvent T D N K := by
  classical
  ext q
  constructor
  · intro hq
    have hinf : (pairNearestHighSet (interpolatedHighPair T q) 0).Infinite :=
      hq.1.1.2
    obtain ⟨Y, hYsub, hYcard⟩ := hinf.exists_subset_card_eq K
    let xOf : Site d → Site d := fun y =>
      if hy : y ∈ Y then Classical.choose
        (exists_low_contact_distance_of_mem_nearest hq (hYsub hy)) else 0
    have hxOf (y : Site d) (hy : y ∈ Y) :
        xOf y ∈ pairLowInfiniteVertices (interpolatedHighPair T q) ∧
          l1dist d (xOf y) y = D := by
      dsimp only [xOf]
      rw [dif_pos hy]
      exact Classical.choose_spec
        (exists_low_contact_distance_of_mem_nearest hq (hYsub hy))
    let F : Finset (Site d) := Y.image xOf ∪ Y
    obtain ⟨N, hN⟩ := StatMech.Lattice.finite_subset_box
      (↑F : Set (Site d)) F.finite_toSet
    apply Set.mem_iUnion.mpr
    refine ⟨N, hq, ?_⟩
    rw [← hYcard]
    let G : Finset (Site d × Site d) := Y.image fun y => (xOf y, y)
    have hGcard : G.card = Y.card := by
      apply Finset.card_image_of_injective
      intro y z hyz
      exact congrArg Prod.snd hyz
    rw [← hGcard]
    apply Finset.card_le_card
    intro p hp
    change p ∈ Y.image (fun y => (xOf y, y)) at hp
    rw [Finset.mem_image] at hp
    obtain ⟨y, hyY, rfl⟩ := hp
    rw [step3WindowContacts, Finset.mem_filter]
    have hyF : y ∈ F := Finset.mem_union_right _ hyY
    have hxF : xOf y ∈ F :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem xOf hyY)
    have hyBox : y ∈ boxFinsetBK d N := by
      rw [mem_boxFinsetBK_iff]
      exact hN hyF
    have hxBox : xOf y ∈ boxFinsetBK d N := by
      rw [mem_boxFinsetBK_iff]
      exact hN hxF
    refine ⟨Finset.mem_product.mpr ⟨hxBox, hyBox⟩, ?_⟩
    exact ⟨(hxOf y hyY).1, hYsub hyY, (hxOf y hyY).2⟩
  · intro hq
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hq
    exact hN.1


end StatMech.FrontierA
