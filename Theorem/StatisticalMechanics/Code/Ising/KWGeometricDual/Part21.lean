/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part21
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_minimalEven_nonOuter_reachable {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (outer : V)
    (hne : Nonempty E) (heven : kwg_IsEven ends Finset.univ)
    (hmin : ∀ S : Finset E, S.Nonempty → kwg_IsEven ends S → S = Finset.univ)
    {v w : V} (hvout : v ≠ outer) (hwout : w ≠ outer)
    (hvinc : ∃ e : E, kwg_incidentMod2 v (ends e))
    (hwinc : ∃ e : E, kwg_incidentMod2 w (ends e)) :
    (kwg_deleteVertexGraph (kwg_faceSupportGraph ends) outer).Reachable v w := by
  classical
  let H := kwg_deleteVertexGraph (kwg_faceSupportGraph ends) outer
  let inC : V → Prop := fun z => z ≠ outer ∧ H.Reachable v z
  let S : Finset E := Finset.univ.filter fun e =>
    inC (ends e).out.1 ∨ inC (ends e).out.2
  have hC_v : inC v := ⟨hvout, SimpleGraph.Reachable.refl _⟩
  have incident_end {z : V} {e : E} (hinc : kwg_incidentMod2 z (ends e)) :
      z = (ends e).out.1 ∨ z = (ends e).out.2 := by
    have hout : ends e = s((ends e).out.1, (ends e).out.2) := (ends e).out_eq.symm
    rw [hout, kwg_incidentMod2_mk] at hinc
    rcases hinc with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have incident_ne {z : V} {e : E} (hinc : kwg_incidentMod2 z (ends e)) :
      (ends e).out.1 ≠ (ends e).out.2 := by
    intro heq
    have hout : ends e = s((ends e).out.1, (ends e).out.2) := (ends e).out_eq.symm
    rw [hout, heq, kwg_incidentMod2_mk] at hinc
    tauto
  have close_edge {a b : V} {e : E} (ha : inC a) (hbout : b ≠ outer)
      (hab : a ≠ b) (he : ends e = s(a, b)) : inC b := by
    refine ⟨hbout, ha.2.trans ?_⟩
    exact (show H.Adj a b from
      ⟨⟨hab, e, he⟩, ha.1, hbout⟩).reachable
  have hSne : S.Nonempty := by
    obtain ⟨e, he⟩ := hvinc
    refine ⟨e, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ e, ?_⟩
    rcases incident_end he with hv | hv
    · exact Or.inl (hv ▸ hC_v)
    · exact Or.inr (hv ▸ hC_v)
  have hnonouter : ∀ z : V, z ≠ outer →
      (S.filter (fun e => kwg_incidentMod2 z (ends e))).card =
        (if inC z then (Finset.univ.filter
          (fun e => kwg_incidentMod2 z (ends e))).card else 0) := by
    intro z hzout
    by_cases hzC : inC z
    · rw [if_pos hzC]
      congr 1
      ext e
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hinc
        refine ⟨?_, hinc⟩
        rcases incident_end hinc with hz | hz
        · exact Or.inl (hz ▸ hzC)
        · exact Or.inr (hz ▸ hzC)
    · rw [if_neg hzC]
      have hempty : S.filter (fun e => kwg_incidentMod2 z (ends e)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e heS hinc
        rw [Finset.mem_filter] at heS
        have hne := incident_ne hinc
        rcases heS.2 with h1 | h2
        · rcases incident_end hinc with hz1 | hz2
          · exact hzC (hz1 ▸ h1)
          · have hout2 : (ends e).out.2 ≠ outer := hz2 ▸ hzout
            exact hzC (hz2 ▸ close_edge h1 hout2 hne (ends e).out_eq.symm)
        · rcases incident_end hinc with hz1 | hz2
          · have hout1 : (ends e).out.1 ≠ outer := hz1 ▸ hzout
            exact hzC (hz1 ▸ close_edge h2 hout1 hne.symm
              ((ends e).out_eq.symm.trans Sym2.eq_swap))
          · exact hzC (hz2 ▸ h2)
      rw [hempty]
      rfl
  have hSeven : kwg_IsEven ends S := by
    intro z
    by_cases hz : z = outer
    · subst z
      change Even (kwg_degree ends S outer)
      have hsum := kwg_sum_degree_even ends S
      have hrest : Even (∑ z : V, if z = outer then 0 else kwg_degree ends S z) := by
        apply Finset.even_sum
        intro z _
        by_cases hz : z = outer
        · simp [hz]
        · simp only [hz, if_false]
          change Even ((S.filter (fun e => kwg_incidentMod2 z (ends e))).card)
          rw [hnonouter z hz]
          by_cases hzC : inC z
          · simpa [hzC] using heven z
          · simp [hzC]
      obtain ⟨a, ha⟩ := hsum
      obtain ⟨b, hb⟩ := hrest
      refine ⟨a - b, ?_⟩
      have hsplit : (∑ z : V, kwg_degree ends S z) =
          kwg_degree ends S outer + ∑ z : V, if z = outer then 0 else kwg_degree ends S z := by
        rw [← Finset.sum_erase_add (Finset.univ : Finset V)
          (fun z => kwg_degree ends S z) (Finset.mem_univ outer), add_comm]
        congr 1
        have hfun : (fun z : V => if z = outer then 0 else kwg_degree ends S z) =
            fun z : V => if z ≠ outer then kwg_degree ends S z else 0 := by
          funext z
          by_cases hz : z = outer <;> simp [hz]
        rw [hfun, ← Finset.sum_filter]
        congr 1
        ext z
        simp [Finset.mem_erase]
      omega
    · rw [hnonouter z hz]
      by_cases hzC : inC z
      · simpa [hzC] using heven z
      · simp [hzC]
  have hSall : S = Finset.univ := hmin S hSne hSeven
  obtain ⟨e, he⟩ := hwinc
  have heS : e ∈ S := hSall.symm ▸ Finset.mem_univ e
  rw [Finset.mem_filter] at heS
  have hne := incident_ne he
  rcases incident_end he with hw | hw <;> rcases heS.2 with h1 | h2
  · simpa [inC, hw] using h1.2
  · have hout1 : (ends e).out.1 ≠ outer := hw ▸ hwout
    simpa [inC, hw] using (close_edge h2 hout1 hne.symm
      ((ends e).out_eq.symm.trans Sym2.eq_swap)).2
  · have hout2 : (ends e).out.2 ≠ outer := hw ▸ hwout
    simpa [inC, hw] using (close_edge h1 hout2 hne (ends e).out_eq.symm).2
  · simpa [inC, hw] using h2.2


theorem kwg_minimalEvenFinset_nonOuter_reachable {V E : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) (outer : V)
    (hne : F.Nonempty) (heven : kwg_IsEven ends F)
    (hmin : ∀ S : Finset E, S ⊆ F → S.Nonempty → kwg_IsEven ends S → S = F)
    {v w : V} (hvout : v ≠ outer) (hwout : w ≠ outer)
    (hvinc : ∃ e ∈ F, kwg_incidentMod2 v (ends e))
    (hwinc : ∃ e ∈ F, kwg_incidentMod2 w (ends e)) :
    (kwg_deleteVertexGraph
      (kwg_faceSupportGraph (fun e : ↑F => ends e.1)) outer).Reachable v w := by
  classical
  let emb : ↑F ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
  let e0 : E := hne.choose
  letI : Nonempty ↑F := ⟨⟨e0, hne.choose_spec⟩⟩
  have heven' : kwg_IsEven (fun e : ↑F => ends e.1) Finset.univ := by
    intro z
    have hz := heven z
    have hmap : ((Finset.univ : Finset ↑F).filter
        (fun e => kwg_incidentMod2 z (ends e.1))).map emb =
        F.filter (fun e => kwg_incidentMod2 z (ends e)) := by
      ext e
      simp [emb, and_comm]
    have hcard := congrArg Finset.card hmap
    rw [Finset.card_map] at hcard
    exact hcard.symm ▸ hz
  have hmin' : ∀ S : Finset ↑F, S.Nonempty →
      kwg_IsEven (fun e : ↑F => ends e.1) S → S = Finset.univ := by
    intro S hSne hSeven
    let T : Finset E := S.map emb
    have hTsub : T ⊆ F := by
      intro e he
      simp only [T, Finset.mem_map] at he
      obtain ⟨e', _, rfl⟩ := he
      exact e'.2
    have hTne : T.Nonempty := Finset.map_nonempty.mpr hSne
    have hTeven : kwg_IsEven ends T := by
      intro z
      have hz := hSeven z
      have hmap : (S.filter (fun e => kwg_incidentMod2 z (ends e.1))).map emb =
          T.filter (fun e => kwg_incidentMod2 z (ends e)) := by
        ext e
        simp [T, emb, and_comm]
      have hcard := congrArg Finset.card hmap
      rw [Finset.card_map] at hcard
      exact hcard ▸ hz
    have hTF : T = F := hmin T hTsub hTne hTeven
    apply Finset.eq_univ_iff_forall.mpr
    intro e
    have heT : (e : E) ∈ T := hTF.symm ▸ e.2
    simp only [T, Finset.mem_map] at heT
    obtain ⟨e', he'S, he'eq⟩ := heT
    have : e' = e := Subtype.ext he'eq
    simpa [this] using he'S
  apply kwg_minimalEven_nonOuter_reachable (fun e : ↑F => ends e.1) outer
    inferInstance heven' hmin' hvout hwout
  · obtain ⟨e, heF, he⟩ := hvinc
    exact ⟨⟨e, heF⟩, he⟩
  · obtain ⟨e, heF, he⟩ := hwinc
    exact ⟨⟨e, heF⟩, he⟩


theorem kwg_exists_minimalEvenFinset_subset_mem {V E : Type*} [DecidableEq E]
    (ends : E → Sym2 V) {F : Finset E} {e : E} (heF : e ∈ F)
    (hF : kwg_IsEven ends F) :
    ∃ S : Finset E, S ⊆ F ∧ e ∈ S ∧ S.Nonempty ∧ kwg_IsEven ends S ∧
      ∀ T : Finset E, T ⊆ S → T.Nonempty → kwg_IsEven ends T → T = S := by
  classical
  let C := F.powerset.filter (fun S => e ∈ S ∧ kwg_IsEven ends S)
  have hFC : F ∈ C := by
    simp [C, heF, hF]
  have hCne : C.Nonempty := ⟨F, hFC⟩
  let cards := C.image Finset.card
  have hcardsne : cards.Nonempty := Finset.image_nonempty.mpr hCne
  let m := cards.min' hcardsne
  have hm : m ∈ cards := Finset.min'_mem cards hcardsne
  obtain ⟨S, hSC, hSm⟩ := Finset.mem_image.mp hm
  have hSprops := Finset.mem_filter.mp hSC
  have hSsub : S ⊆ F := Finset.mem_powerset.mp hSprops.1
  have heS : e ∈ S := hSprops.2.1
  have hSeven : kwg_IsEven ends S := hSprops.2.2
  have hSne : S.Nonempty := ⟨e, heS⟩
  refine ⟨S, hSsub, heS, hSne, hSeven, ?_⟩
  intro T hTS hTne hTeven
  have hmS : m = S.card := hSm.symm
  by_cases heT : e ∈ T
  · have hTC : T ∈ C := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (hTS.trans hSsub), heT, hTeven⟩
    have hTcard : T.card ∈ cards := Finset.mem_image.mpr ⟨T, hTC, rfl⟩
    have hminle : m ≤ T.card := Finset.min'_le cards T.card hTcard
    apply Finset.eq_of_subset_of_card_le hTS
    simpa [hmS] using hminle
  · let R := S \ T
    have hReven : kwg_IsEven ends R :=
      kwg_IsEven_sdiff ends hTS hSeven hTeven
    have heR : e ∈ R := by simp [R, heS, heT]
    have hRsub : R ⊆ F := Finset.sdiff_subset.trans hSsub
    have hRC : R ∈ C := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr hRsub, heR, hReven⟩
    have hRcard : R.card ∈ cards := Finset.mem_image.mpr ⟨R, hRC, rfl⟩
    have hminle : m ≤ R.card := Finset.min'_le cards R.card hRcard
    have hcard := Finset.card_sdiff_add_card_eq_card hTS
    change R.card + T.card = S.card at hcard
    have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
    omega


theorem kwg_exists_minimalEvenFinset_peel_mem {V E : Type*} [DecidableEq E]
    (ends : E → Sym2 V) {F : Finset E} {e : E} (heF : e ∈ F)
    (hF : kwg_IsEven ends F) :
    ∃ S R : Finset E,
      S ⊆ F ∧ e ∈ S ∧ S.Nonempty ∧ kwg_IsEven ends S ∧
        (∀ T : Finset E, T ⊆ S → T.Nonempty →
          kwg_IsEven ends T → T = S) ∧
        R = F \ S ∧ kwg_IsEven ends R ∧ Disjoint S R ∧ S ∪ R = F := by
  obtain ⟨S, hSF, heS, hSne, hSeven, hSmin⟩ :=
    kwg_exists_minimalEvenFinset_subset_mem ends heF hF
  let R := F \ S
  have hReven : kwg_IsEven ends R :=
    kwg_IsEven_sdiff ends hSF hF hSeven
  have hdisjoint : Disjoint S R := by
    simpa [R] using (Finset.disjoint_sdiff : Disjoint S (F \ S))
  have hunion : S ∪ R = F := by
    simpa [R, Finset.union_comm] using Finset.sdiff_union_of_subset hSF
  exact ⟨S, R, hSF, heS, hSne, hSeven, hSmin, rfl,
    hReven, hdisjoint, hunion⟩


theorem kwg_subdivGraph_face_degree_even {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (heven : kwg_IsEven ends Finset.univ) (v : V) :
    Even ((kwg_subdivGraph ends).degree (Sum.inl v)) := by
  classical
  rw [kwg_subdivGraph_face_degree]
  let A := (Finset.univ : Finset E).filter (fun e => (ends e).out.1 = v)
  let B := (Finset.univ : Finset E).filter (fun e => (ends e).out.2 = v)
  let I := (Finset.univ : Finset E).filter
    (fun e => kwg_incidentMod2 v (ends e))
  let L := (Finset.univ : Finset E).filter
    (fun e => (ends e).out.1 = v ∧ (ends e).out.2 = v)
  have hcount : A.card + B.card = I.card + 2 * L.card := by
    rw [kwg_card_filter_eq_sum_ite, kwg_card_filter_eq_sum_ite,
      kwg_card_filter_eq_sum_ite, kwg_card_filter_eq_sum_ite]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ e : E, ((if (ends e).out.1 = v then 1 else 0) +
          if (ends e).out.2 = v then 1 else 0) =
          ∑ e : E, ((if kwg_incidentMod2 v (ends e) then 1 else 0) +
            2 * if (ends e).out.1 = v ∧ (ends e).out.2 = v then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro e _
        have hout : ends e = s((ends e).out.1, (ends e).out.2) := (ends e).out_eq.symm
        have hinc : kwg_incidentMod2 v (ends e) ↔
            ((ends e).out.1 = v ∧ (ends e).out.2 ≠ v) ∨
              ((ends e).out.2 = v ∧ (ends e).out.1 ≠ v) := by
          conv_lhs => rw [hout]
          exact kwg_incidentMod2_mk v (ends e).out.1 (ends e).out.2
        by_cases h1 : (ends e).out.1 = v <;>
          by_cases h2 : (ends e).out.2 = v <;> simp [hinc, h1, h2]
      _ = (∑ e : E, if kwg_incidentMod2 v (ends e) then 1 else 0) +
          ∑ e : E, 2 * if (ends e).out.1 = v ∧ (ends e).out.2 = v then 1 else 0 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ e : E, if kwg_incidentMod2 v (ends e) then 1 else 0) +
          2 * ∑ e : E, if (ends e).out.1 = v ∧ (ends e).out.2 = v then 1 else 0 := by
        rw [Finset.mul_sum]
  rw [show ((Finset.univ : Finset E).filter (fun e => (ends e).out.1 = v)).card = A.card
      from rfl,
    show ((Finset.univ : Finset E).filter (fun e => (ends e).out.2 = v)).card = B.card
      from rfl,
    hcount]
  obtain ⟨k, hk⟩ := heven v
  change Even (I.card + 2 * L.card)
  have hI : I.card = k + k := hk
  exact ⟨k + L.card, by omega⟩


theorem kwg_subdivGraph_reachable_port_of_incident {V E : Type*}
    (ends : E → Sym2 V) {v : V} {e : E}
    (hinc : kwg_incidentMod2 v (ends e)) (b : Bool) :
    (kwg_subdivGraph ends).Reachable (Sum.inl v) (Sum.inr (e, b)) := by
  have hout : ends e = s((ends e).out.1, (ends e).out.2) := (ends e).out_eq.symm
  rw [hout, kwg_incidentMod2_mk] at hinc
  rcases hinc with ⟨h1, _⟩ | ⟨h2, _⟩
  · subst v
    cases b
    · exact SimpleGraph.Adj.reachable
        ((kwg_subdivGraph_face_port_false ends _ _).2 rfl)
    · exact (SimpleGraph.Adj.reachable
          ((kwg_subdivGraph_face_port_false ends _ _).2 rfl)).trans
        (SimpleGraph.Adj.reachable
          ((kwg_subdivGraph_ports ends e e false true).2 ⟨rfl, by decide⟩))
  · subst v
    cases b
    · exact (SimpleGraph.Adj.reachable
          ((kwg_subdivGraph_face_port_true ends _ _).2 rfl)).trans
        (SimpleGraph.Adj.reachable
          ((kwg_subdivGraph_ports ends e e true false).2 ⟨rfl, by decide⟩))
    · exact SimpleGraph.Adj.reachable
        ((kwg_subdivGraph_face_port_true ends _ _).2 rfl)


theorem kwg_minimalEven_edgePorts_reachable {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (hne : Nonempty E) (heven : kwg_IsEven ends Finset.univ)
    (hmin : ∀ S : Finset E, S.Nonempty → kwg_IsEven ends S → S = Finset.univ) :
    ∀ e e' : E, ∀ b b' : Bool,
      (kwg_subdivGraph ends).Reachable (Sum.inr (e, b)) (Sum.inr (e', b')) := by
  classical
  let e0 : E := Classical.choice hne
  let G := kwg_subdivGraph ends
  let c := G.connectedComponentMk (Sum.inr (e0, false))
  let S : Finset E := Finset.univ.filter fun e => Sum.inr (e, false) ∈ c.supp
  have hports : ∀ e : E, e ∈ S ↔ Sum.inr (e, false) ∈ c.supp := by
    intro e
    simp [S]
  have hSne : S.Nonempty := by
    refine ⟨e0, (hports e0).2 ?_⟩
    simp [c]
  have hSeven : kwg_IsEven ends S := by
    intro v
    by_cases hv : Sum.inl v ∈ c.supp
    · have hfilter : S.filter (fun e => kwg_incidentMod2 v (ends e)) =
          (Finset.univ : Finset E).filter (fun e => kwg_incidentMod2 v (ends e)) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro hinc
          refine ⟨(hports e).2 ?_, hinc⟩
          have hvc := (SimpleGraph.ConnectedComponent.mem_supp_iff c (Sum.inl v)).mp hv
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff c,
            ← hvc, SimpleGraph.ConnectedComponent.eq]
          exact (kwg_subdivGraph_reachable_port_of_incident ends hinc false).symm
      rw [hfilter]
      exact heven v
    · have hfilter : S.filter (fun e => kwg_incidentMod2 v (ends e)) = ∅ := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨heS, hinc⟩
          exfalso
          apply hv
          have hec := (SimpleGraph.ConnectedComponent.mem_supp_iff c
            (Sum.inr (e, false))).mp ((hports e).1 heS)
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff c,
            ← hec, SimpleGraph.ConnectedComponent.eq]
          exact kwg_subdivGraph_reachable_port_of_incident ends hinc false
        · intro he
          simp at he
      rw [hfilter]
      exact Even.zero
  have hSall : S = Finset.univ := hmin S hSne hSeven
  intro e e' b b'
  have he0 : G.Reachable (Sum.inr (e, false)) (Sum.inr (e0, false)) := by
    rw [← SimpleGraph.ConnectedComponent.eq,
      ← SimpleGraph.ConnectedComponent.mem_supp_iff]
    change Sum.inr (e, false) ∈ c.supp
    exact (hports e).1 (hSall.symm ▸ Finset.mem_univ e)
  have he'0 : G.Reachable (Sum.inr (e', false)) (Sum.inr (e0, false)) := by
    rw [← SimpleGraph.ConnectedComponent.eq,
      ← SimpleGraph.ConnectedComponent.mem_supp_iff]
    change Sum.inr (e', false) ∈ c.supp
    exact (hports e').1 (hSall.symm ▸ Finset.mem_univ e')
  have hb0 : G.Reachable (Sum.inr (e, b)) (Sum.inr (e, false)) := by
    cases b
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (by simp [G])
  have hb'0 : G.Reachable (Sum.inr (e', b')) (Sum.inr (e', false)) := by
    cases b'
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (by simp [G])
  exact hb0.trans (he0.trans (he'0.symm.trans hb'0.symm))


theorem kwg_cutEvenMatching_of_duality (P : PlanarZ2Subgraph) (t mult : ℝ)
    (hdual : kwg_GeometricCutCycleDuality P)
    (hfib : ∀ F : Finset (kwg_Edge P), kwg_IsEven (kwg_dualEnds P) F →
      ((Finset.univ.filter (fun c : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) c = F)).card : ℝ) = mult) :
    kwg_GeometricCutEvenMatching P t mult := by
  classical
  unfold kwg_GeometricCutEvenMatching kwg_CutEvenMatching
  rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset (ConfigSpace P.V)))
    (g := fun c => kwg_cutSet (kwg_primalEnds P) c)
    (f := fun c => t ^ (kwg_cutSet (kwg_primalEnds P) c).card)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  have hinter :
      (∑ c ∈ (Finset.univ : Finset (ConfigSpace P.V)) with
          kwg_cutSet (kwg_primalEnds P) c = F,
          t ^ (kwg_cutSet (kwg_primalEnds P) c).card) =
        ((Finset.univ.filter (fun c : ConfigSpace P.V =>
          kwg_cutSet (kwg_primalEnds P) c = F)).card : ℝ) * t ^ F.card := by
    calc
      _ = ∑ _c ∈ (Finset.univ.filter (fun c : ConfigSpace P.V =>
          kwg_cutSet (kwg_primalEnds P) c = F)), t ^ F.card := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.mem_filter] at hc
            rw [hc.2]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hinter]
  by_cases hev : kwg_IsEven (kwg_dualEnds P) F
  · rw [if_pos hev, hfib F hev]
  · rw [if_neg hev, mul_zero]
    have hempty : Finset.univ.filter (fun c : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) c = F) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro c _ hc
      exact hev ((hdual F).mpr ⟨c, hc⟩)
    rw [hempty, Finset.card_empty]
    norm_num


theorem kwg_geometricCutEvenMatching (P : PlanarZ2Subgraph) (t : ℝ) :
    kwg_GeometricCutEvenMatching P t
      ((2 : ℝ) ^ Nat.card P.G.ConnectedComponent) := by
  classical
  apply kwg_cutEvenMatching_of_duality P t
    ((2 : ℝ) ^ Nat.card P.G.ConnectedComponent) (kwg_geometricCutCycleDuality P)
  intro F hev
  obtain ⟨c, hc⟩ := (kwg_geometricCutCycleDuality P F).mp hev
  have hfilter :
      Finset.univ.filter (fun d : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) d = F) =
      Finset.univ.filter (fun d : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hc]
  rw [hfilter, kwg_primalCut_fiber_card]
  norm_num


theorem kwg_geometricCutEvenMatching_of_connected (P : PlanarZ2Subgraph)
    (hconn : P.G.Connected) (t : ℝ) : kwg_GeometricCutEvenMatching P t 2 := by
  classical
  letI : Nonempty P.V := hconn.nonempty
  apply kwg_cutEvenMatching_of_duality P t 2 (kwg_geometricCutCycleDuality P)
  intro F hev
  obtain ⟨c, hc⟩ := (kwg_geometricCutCycleDuality P F).mp hev
  have hfilter :
      Finset.univ.filter (fun d : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) d = F) =
      Finset.univ.filter (fun d : ConfigSpace P.V => cutEdges P.G d = cutEdges P.G c) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hc, kwg_cutSet_eq_iff_cutEdges_eq]
  rw [hfilter]
  exact_mod_cast fiber_card_eq_two P.G hconn.preconnected rfl


end Ising
end StatMech
