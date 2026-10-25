/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part3


namespace StatMech.FrontierA

theorem exists_secondCollisionCharge_of_card_le
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A ↪ C) (g : B ↪ C)
    (first : crossCollision f g ↪ C)
    (hfirstFreshLeft : ∀ collision a, first collision ≠ f a)
    (hcard : Fintype.card A + Fintype.card B ≤ Fintype.card C) :
    ∃ second : crossCollision first g ↪ C,
      (∀ collision a, second collision ≠ f a) ∧
      (∀ collision b, second collision ≠ g b) ∧
      ∀ collision old, second collision ≠ first old := by
  classical
  letI : Fintype (crossCollision f g) :=
    Fintype.ofInjective (fun collision => collision.1.1)
      (crossCollision_fst_injective f g)
  letI : Fintype (crossCollision first g) :=
    Fintype.ofInjective (fun collision => collision.1.1)
      (crossCollision_fst_injective first g)
  let F : Finset C := Finset.univ.map f
  let G : Finset C := Finset.univ.map g
  let H : Finset C := Finset.univ.map first
  let fgValue : crossCollision f g ↪ C :=
    ⟨fun collision => f collision.1.1, fun x y h =>
      crossCollision_fst_injective f g (f.injective h)⟩
  let hgValue : crossCollision first g ↪ C :=
    ⟨fun collision => first collision.1.1, fun x y h =>
      crossCollision_fst_injective first g (first.injective h)⟩
  have hFG : F ∩ G = Finset.univ.map fgValue := by
    ext c
    simp only [F, G, Finset.mem_inter, Finset.mem_map, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, hab⟩⟩
      exact ⟨⟨(a, b), hab.symm⟩, rfl⟩
    · rintro ⟨collision, rfl⟩
      exact ⟨⟨collision.1.1, rfl⟩,
        ⟨collision.1.2, collision.2.symm⟩⟩
  have hFH : F ∩ H = ∅ := by
    ext c
    constructor
    · rintro hc
      obtain ⟨⟨a, ha⟩, ⟨collision, hcollision⟩⟩ := by
        simpa only [F, H, Finset.mem_inter, Finset.mem_map,
          Finset.mem_univ, true_and] using hc
      exact False.elim (hfirstFreshLeft collision a
        (hcollision.trans ha.symm))
    · simp
  have hGH : G ∩ H = Finset.univ.map hgValue := by
    ext c
    simp only [G, H, Finset.mem_inter, Finset.mem_map, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨b, rfl⟩, ⟨old, hold⟩⟩
      exact ⟨⟨(old, b), hold⟩, hold⟩
    · rintro ⟨collision, rfl⟩
      exact ⟨⟨collision.1.2, collision.2.symm⟩,
        ⟨collision.1.1, rfl⟩⟩
  have hUnionInter : (F ∪ G) ∩ H = G ∩ H := by
    ext c
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hFGc, hcH⟩
      rcases hFGc with hcF | hcG
      · exact False.elim (by
          have : c ∈ F ∩ H := Finset.mem_inter.mpr ⟨hcF, hcH⟩
          simpa [hFH] using this)
      · exact ⟨hcG, hcH⟩
    · rintro ⟨hcG, hcH⟩
      exact ⟨Or.inr hcG, hcH⟩
  have hFcard : F.card = Fintype.card A := by simp [F]
  have hGcard : G.card = Fintype.card B := by simp [G]
  have hHcard : H.card = Fintype.card (crossCollision f g) := by simp [H]
  have hFGcard : (F ∩ G).card = Fintype.card (crossCollision f g) := by
    rw [hFG]
    simp
  have hGHcard : (G ∩ H).card =
      Fintype.card (crossCollision first g) := by
    rw [hGH]
    simp
  have hUnionCard : (F ∪ G ∪ H).card +
      Fintype.card (crossCollision first g) =
      Fintype.card A + Fintype.card B := by
    have hFGunion := Finset.card_union_add_card_inter F G
    have hFGHunion := Finset.card_union_add_card_inter (F ∪ G) H
    rw [hFcard, hGcard, hFGcard] at hFGunion
    rw [hUnionInter, hGHcard, hHcard] at hFGHunion
    omega
  let available : Finset C := Finset.univ \ (F ∪ G ∪ H)
  have hAvailableCard : Fintype.card (crossCollision first g) ≤
      available.card := by
    have hsubset : F ∪ G ∪ H ⊆ (Finset.univ : Finset C) := by
      exact fun _ _ => Finset.mem_univ _
    have hsub := Finset.card_sdiff_of_subset hsubset
    change available.card = Fintype.card C - (F ∪ G ∪ H).card at hsub
    omega
  let intoAvailable : crossCollision first g ↪ ↑available :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_coe] using hAvailableCard))
  let second : crossCollision first g ↪ C :=
    intoAvailable.trans ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨second, ?_, ?_, ?_⟩
  · intro collision a heq
    have havail := (intoAvailable collision).2
    have hnotUnion := (Finset.mem_sdiff.mp havail).2
    apply hnotUnion
    apply Finset.mem_union.mpr
    apply Or.inl
    apply Finset.mem_union.mpr
    apply Or.inl
    simpa only [F, Finset.mem_map, Finset.mem_univ, true_and, second] using
      ⟨a, heq.symm⟩
  · intro collision b heq
    have havail := (intoAvailable collision).2
    have hnotUnion := (Finset.mem_sdiff.mp havail).2
    apply hnotUnion
    apply Finset.mem_union.mpr
    apply Or.inl
    apply Finset.mem_union.mpr
    apply Or.inr
    simpa only [G, Finset.mem_map, Finset.mem_univ, true_and, second] using
      ⟨b, heq.symm⟩
  · intro collision old heq
    have havail := (intoAvailable collision).2
    have hnotUnion := (Finset.mem_sdiff.mp havail).2
    apply hnotUnion
    apply Finset.mem_union.mpr
    apply Or.inr
    simpa only [H, Finset.mem_map, Finset.mem_univ, true_and, second] using
      ⟨old, heq.symm⟩


end StatMech.FrontierA
