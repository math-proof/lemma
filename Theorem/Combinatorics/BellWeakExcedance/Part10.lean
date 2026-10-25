/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Def.Combinatorics.BellWeakExcedance.Part10


section

namespace MetaMathlibExt

theorem ofPartPerm_apply {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n} :
    ofPartPerm P u = ofPartFun P u := rfl

theorem orderEmb_symm_mins {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∈ mins P) :
    (mins P).orderEmbOfFin (card_mins_eq P)
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, hu⟩) = u := by
  have h1 : ((mins P).orderIsoOfFin (card_mins_eq P))
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, hu⟩) =
        ⟨u, hu⟩ :=
    OrderIso.apply_symm_apply _ _
  have h2 : ↑(((mins P).orderIsoOfFin (card_mins_eq P))
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, hu⟩)) = u := by
    rw [h1]
  rw [Finset.coe_orderIsoOfFin_apply] at h2
  exact h2

theorem ofPartPerm_le_ofMem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {m : Fin n}
    (hm : m ∈ mins P) : m ≤ ofPartPerm P m := by
  rw [ofPartPerm_apply, ofPartFun_eq_ofMem hm]
  calc m = (mins P).orderEmbOfFin (card_mins_eq P)
          (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hm⟩) :=
          (orderEmb_symm_mins hm).symm
    _ ≤ (maxs P).orderEmbOfFin (card_maxs_eq P)
          (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hm⟩) :=
          interlacing P _

theorem mem_wexSet_ofPartPerm_iff {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n} :
    u ∈ wexSet n (ofPartPerm P) ↔ u ∈ mins P := by
  constructor
  · intro h
    simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
    by_contra hu
    have hlt : ofPartPerm P u < u := by
      rw [ofPartPerm_apply, ofPartFun_eq_pred hu]
      exact pred_lt hu
    exact absurd h (not_le_of_gt hlt)
  · intro h
    simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ofPartPerm_le_ofMem h

theorem ofPartPerm_valid {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    ∀ i j : Fin n, i < j → i ≤ ofPartPerm P i → j ≤ ofPartPerm P j →
      ofPartPerm P i < ofPartPerm P j := by
  intro i j hij hi hj
  have hiM : i ∈ mins P := by
    have hmem : i ∈ wexSet n (ofPartPerm P) := by
      simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    exact (mem_wexSet_ofPartPerm_iff).mp hmem
  have hjM : j ∈ mins P := by
    have hmem : j ∈ wexSet n (ofPartPerm P) := by
      simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj
    exact (mem_wexSet_ofPartPerm_iff).mp hmem
  simp only [ofPartPerm_apply, ofPartFun_eq_ofMem hiM, ofPartFun_eq_ofMem hjM]
  have hIdx : ((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨i, hiM⟩ <
      ((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨j, hjM⟩ := by
    have hEmb : (mins P).orderEmbOfFin (card_mins_eq P)
          (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨i, hiM⟩) <
        (mins P).orderEmbOfFin (card_mins_eq P)
          (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨j, hjM⟩) := by
      rw [orderEmb_symm_mins hiM, orderEmb_symm_mins hjM]
      exact hij
    exact ((mins P).orderEmbOfFin (card_mins_eq P)).lt_iff_lt.mp hEmb
  exact ((maxs P).orderEmbOfFin (card_maxs_eq P)).strictMono hIdx

theorem find_pos_of_notMem {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {i : Fin n} (hi : i ∉ wexSet n σ) :
    0 < Nat.find (exists_hit n σ i) := by
  by_contra h
  push Not at h
  have h0 : Nat.find (exists_hit n σ i) = 0 := by omega
  have hspec := Nat.find_spec (exists_hit n σ i)
  rw [h0] at hspec
  have hmem : i ∈ wexSet n σ := by simpa using hspec
  exact hi hmem

theorem pow_apply_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (m : ℕ) : ⇑(σ ^ m) (⇑σ i) = ⇑(σ ^ (m + 1)) i := by
  rw [pow_succ]
  rfl

theorem root_step {n : ℕ} {σ : Equiv.Perm (Fin n)} {i : Fin n}
    (hi : i ∉ wexSet n σ) : root n σ i = root n σ (⇑σ i) := by
  unfold root
  have hTpos := find_pos_of_notMem hi
  set T := Nat.find (exists_hit n σ i) with hT
  set S := Nat.find (exists_hit n σ (⇑σ i)) with hS
  have hmem : ⇑(σ ^ (T - 1)) (⇑σ i) ∈ wexSet n σ := by
    rw [pow_apply_succ, Nat.sub_add_cancel hTpos]
    exact Nat.find_spec (exists_hit n σ i)
  have hle1 : S ≤ T - 1 := Nat.find_min' _ hmem
  have hle2 : T - 1 ≤ S := by
    by_contra hlt
    push Not at hlt
    have hspec := Nat.find_spec (exists_hit n σ (⇑σ i))
    rw [pow_apply_succ] at hspec
    have hmin := Nat.find_min (exists_hit n σ i) (by omega : S + 1 < T)
    exact hmin hspec
  have hEq : S = T - 1 := le_antisymm hle1 hle2
  have hT : T = S + 1 := by omega
  rw [hT, ← pow_apply_succ]

theorem min'_congr {α : Type*} [LinearOrder α] {s t : Finset α}
    (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst h
  rfl

theorem minOfBlock_eq_of_mem_mins {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∈ mins P) : minOfBlock P u = u := by
  rw [mem_mins_iff] at hu
  obtain ⟨t, ht, hmem, hle⟩ := hu
  have hpart : P.part u = t := P.part_eq_of_mem ht hmem
  have hmin : t.min' (P.nonempty_of_mem_parts ht) = u := by
    apply le_antisymm
    · exact Finset.min'_le _ _ hmem
    · exact hle _ (Finset.min'_mem _ _)
  have hEq : minOfBlock P u = t.min' (P.nonempty_of_mem_parts ht) := by
    unfold minOfBlock
    exact min'_congr hpart _ _
  rw [hEq]
  exact hmin

theorem part_eq_of_mem_part {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {x y : Fin n}
    (h : y ∈ P.part x) : P.part y = P.part x :=
  P.eq_of_mem_parts (P.part_mem.mpr (Finset.mem_univ y))
    (P.part_mem.mpr (Finset.mem_univ x)) (P.mem_part (Finset.mem_univ y)) h

theorem minOfBlock_eq_of_mem_part {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {x y : Fin n}
    (h : y ∈ P.part x) : minOfBlock P y = minOfBlock P x := by
  have hEq := part_eq_of_mem_part h
  unfold minOfBlock
  exact min'_congr hEq _ _

theorem minOfBlock_eq_iff_part_eq {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {a b : Fin n} :
    minOfBlock P a = minOfBlock P b ↔ P.part a = P.part b := by
  constructor
  · intro h
    have ha : minOfBlock P a ∈ P.part a := by
      unfold minOfBlock
      exact Finset.min'_mem _ _
    have hb : minOfBlock P b ∈ P.part b := by
      unfold minOfBlock
      exact Finset.min'_mem _ _
    rw [h] at ha
    exact P.eq_of_mem_parts (P.part_mem.mpr (Finset.mem_univ a))
      (P.part_mem.mpr (Finset.mem_univ b)) ha hb
  · intro h
    unfold minOfBlock
    exact min'_congr h _ _

theorem root_ofPart_eq_minOfBlock {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (u : Fin n) :
    root n (ofPartPerm P) u = minOfBlock P u := by
  have h : ∀ v : ℕ, ∀ w : Fin n, w.val = v →
      root n (ofPartPerm P) w = minOfBlock P w := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro w hw
      by_cases hwM : w ∈ mins P
      · have hwW : w ∈ wexSet n (ofPartPerm P) :=
          mem_wexSet_ofPartPerm_iff.mpr hwM
        rw [root_eq_self _ _ _ hwW, minOfBlock_eq_of_mem_mins hwM]
      · have hwW : w ∉ wexSet n (ofPartPerm P) := fun h =>
          hwM (mem_wexSet_ofPartPerm_iff.mp h)
        have hEq : ofPartPerm P w = pred P w hwM := by
          rw [ofPartPerm_apply, ofPartFun_eq_pred hwM]
        have hlt : ofPartPerm P w < w := hEq ▸ pred_lt hwM
        have hval : (ofPartPerm P w).val < v := by
          have hltV : (ofPartPerm P w).val < w.val := hlt
          omega
        have hIH := ih (ofPartPerm P w).val hval (ofPartPerm P w) rfl
        have hmem : ofPartPerm P w ∈ P.part w := hEq ▸ pred_mem hwM
        have hminEq := minOfBlock_eq_of_mem_part hmem
        calc root n (ofPartPerm P) w
            = root n (ofPartPerm P) (⇑(ofPartPerm P) w) := root_step hwW
          _ = minOfBlock P w := by rw [hIH]; exact hminEq
  exact h u.val u rfl

theorem part_eq_toPart_ofPartPerm {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (a : Fin n) :
    (toPart n (ofPartPerm P)).part a = P.part a := by
  ext b
  rw [mem_toPart_iff, root_ofPart_eq_minOfBlock, root_ofPart_eq_minOfBlock,
    minOfBlock_eq_iff_part_eq]
  exact eq_comm.trans
    (P.mem_part_iff_part_eq_part (Finset.mem_univ b)
      (Finset.mem_univ a)).symm

theorem toPart_ofPartPerm {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    toPart n (ofPartPerm P) = P := by
  apply finpartition_eq_of_parts_eq
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha⟩ := (toPart n (ofPartPerm P)).nonempty_of_mem_parts ht
    have hEq := part_eq_toPart_ofPartPerm P a
    have hpart : (toPart n (ofPartPerm P)).part a = t :=
      (toPart n (ofPartPerm P)).part_eq_of_mem ht ha
    rw [hEq] at hpart
    rw [← hpart]
    exact P.part_mem.mpr (Finset.mem_univ a)
  · intro ht
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts ht
    have hEq := part_eq_toPart_ofPartPerm P a
    have hpart : P.part a = t := P.part_eq_of_mem ht ha
    have hQ : (toPart n (ofPartPerm P)).part a = t := hEq.trans hpart
    rw [← hQ]
    exact (toPart n (ofPartPerm P)).part_mem.mpr (Finset.mem_univ a)

theorem pred_eq_of_injective {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (g : Fin n → Fin n)
    (hinj : Function.Injective g)
    (hmem : ∀ u : Fin n, u ∉ mins P → g u ∈ P.part u)
    (hlt : ∀ u : Fin n, u ∉ mins P → g u < u)
    (u : Fin n) (hu : u ∉ mins P) : g u = pred P u hu := by
  have h : ∀ v : ℕ, ∀ w : Fin n, w.val = v → ∀ hw : w ∉ mins P,
      g w = pred P w hw := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro w hw hwM
      have hle : g w ≤ pred P w hwM :=
        le_pred_of_mem hwM (hmem w hwM) (hlt w hwM)
      rcases lt_or_eq_of_le hle with hlt2 | hEq
      · have hgu : g w ∈ P.part w := hmem w hwM
        have hpartEq : P.part (g w) = P.part w :=
          part_eq_of_mem_part hgu
        have hy : g w ∉ maxs P := by
          intro hmax
          rw [mem_maxs_iff] at hmax
          obtain ⟨t, ht, hmem2, hle2⟩ := hmax
          have htEq : t = P.part w :=
            ((P.part_eq_of_mem ht hmem2).symm.trans hpartEq)
          have hmemP : pred P w hwM ∈ t := by
            rw [htEq]
            exact pred_mem hwM
          have hle3 : pred P w hwM ≤ g w := hle2 _ hmemP
          exact absurd hle3 (not_le_of_gt hlt2)
        have hpu : pred P w hwM ∈ P.part (g w) := by
          rw [hpartEq]
          exact pred_mem hwM
        set vv : Fin n := succ P (g w) hy with hvv
        have hleV : vv ≤ pred P w hwM := succ_le_of_mem hy hpu hlt2
        have hltV : vv < w :=
          lt_of_le_of_lt hleV (pred_lt hwM)
        have hvU : vv ∈ P.part w := by
          rw [← hpartEq]
          exact succ_mem hy
        have hvM : vv ∉ mins P := by
          intro hmemM
          have hEq1 : minOfBlock P vv = vv :=
            minOfBlock_eq_of_mem_mins hmemM
          have hEq2 : minOfBlock P vv = minOfBlock P w :=
            minOfBlock_eq_of_mem_part hvU
          have hleMin : minOfBlock P w ≤ g w := by
            unfold minOfBlock
            exact Finset.min'_le _ _ hgu
          have hvvEq : vv = minOfBlock P w := hEq1.symm.trans hEq2
          have hcon : vv ≤ g w := by
            rw [hvvEq]
            exact hleMin
          have hltS : g w < vv := lt_succ hy
          exact absurd hcon (not_le_of_gt hltS)
        have hval : vv.val < v := by
          have hltW : vv.val < w.val := hltV
          omega
        have hgv : g vv = pred P vv hvM := ih vv.val hval vv rfl hvM
        have hps : pred P vv hvM = g w := pred_succ_eq hy
        have hcon : g vv = g w := hgv.trans hps
        exact absurd (hinj hcon) (ne_of_lt hltV)
      · exact hEq
  exact h u.val u rfl hu

theorem perm_eq_pred_of_notMem {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {u : Fin n} (hu : u ∉ mins (toPart n σ)) :
    ⇑σ u = pred (toPart n σ) u hu := by
  have hW : wexSet n σ = mins (toPart n σ) := wexSet_eq_mins_toPart n σ
  have hinj : Function.Injective ⇑σ := σ.injective
  have hmem : ∀ v : Fin n, v ∉ mins (toPart n σ) →
      ⇑σ v ∈ (toPart n σ).part v := by
    intro v hv
    have hvW : v ∉ wexSet n σ := fun h => hv (hW ▸ h)
    rw [mem_toPart_iff]
    exact root_step hvW
  have hlt : ∀ v : Fin n, v ∉ mins (toPart n σ) → ⇑σ v < v := by
    intro v hv
    have hvW : v ∉ wexSet n σ := fun h => hv (hW ▸ h)
    simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hvW
    exact lt_of_not_ge hvW
  exact pred_eq_of_injective (toPart n σ) ⇑σ hinj hmem hlt u hu

theorem perm_maps_wex_to_maxs {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {r : Fin n} (hr : r ∈ wexSet n σ) :
    ⇑σ r ∈ maxs (toPart n σ) := by
  have hW : wexSet n σ = mins (toPart n σ) := wexSet_eq_mins_toPart n σ
  set P : Finpartition (Finset.univ : Finset (Fin n)) := toPart n σ with hP
  set A : Finset (Fin n) := Finset.univ \ wexSet n σ with hA
  set B : Finset (Fin n) := Finset.univ \ maxs P with hB
  have hmaps : ∀ u ∈ A, ⇑σ u ∈ B := by
    intro u hu
    simp only [hA, Finset.mem_sdiff, Finset.mem_univ, true_and] at hu
    have huM : u ∉ mins P := by
      intro hcon
      apply hu
      rw [hW]
      exact hcon
    have hEq : ⇑σ u = pred P u huM := perm_eq_pred_of_notMem huM
    rw [hB, Finset.mem_sdiff]
    constructor
    · exact Finset.mem_univ _
    · rw [hEq]
      exact pred_not_mem_maxs huM
  have hcardW : (wexSet n σ).card = P.parts.card := by
    rw [hW]
    exact card_mins_eq P
  have hcardM : (maxs P).card = P.parts.card := card_maxs_eq P
  have hcardA : A.card = n - P.parts.card := by
    rw [hA, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hcardW]
  have hcardB : B.card = n - P.parts.card := by
    rw [hB, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hcardM]
  have himg_sub : A.image ⇑σ ⊆ B := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact hmaps u hu
  have himg_card : (A.image ⇑σ).card = B.card := by
    rw [Finset.card_image_of_injective A σ.injective, hcardA, hcardB]
  have himg_eq : A.image ⇑σ = B :=
    Finset.eq_of_subset_of_card_le himg_sub himg_card.ge
  by_contra hnot
  have hrB : ⇑σ r ∈ B := by
    rw [hB, Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, hnot⟩
  rw [← himg_eq, Finset.mem_image] at hrB
  obtain ⟨u, hu, hEq⟩ := hrB
  have hEq2 : u = r := σ.injective hEq
  subst hEq2
  rw [hA, Finset.mem_sdiff] at hu
  exact hu.2 hr

theorem bwe_perm_mins_to_maxs {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j : Fin n, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j) :
    (fun x : Fin (toPart n σ).parts.card =>
      σ ((mins (toPart n σ)).orderEmbOfFin (card_mins_eq (toPart n σ)) x)) =
      (maxs (toPart n σ)).orderEmbOfFin (card_maxs_eq (toPart n σ)) := by
  apply Finset.orderEmbOfFin_unique (card_maxs_eq (toPart n σ))
  · intro x
    apply perm_maps_wex_to_maxs
    rw [wexSet_eq_mins_toPart]
    exact Finset.orderEmbOfFin_mem _ _ _
  · intro a b hab
    apply hσ
    · exact ((mins (toPart n σ)).orderEmbOfFin
        (card_mins_eq (toPart n σ))).strictMono hab
    · have ha : (mins (toPart n σ)).orderEmbOfFin
          (card_mins_eq (toPart n σ)) a ∈ wexSet n σ := by
        rw [wexSet_eq_mins_toPart]
        exact Finset.orderEmbOfFin_mem _ _ _
      simpa only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    · have hb : (mins (toPart n σ)).orderEmbOfFin
          (card_mins_eq (toPart n σ)) b ∈ wexSet n σ := by
        rw [wexSet_eq_mins_toPart]
        exact Finset.orderEmbOfFin_mem _ _ _
      simpa only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hb

theorem bwe_ofPartPerm_toPart {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j : Fin n, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j) :
    ofPartPerm (toPart n σ) = σ := by
  apply Equiv.ext
  intro u
  rw [ofPartPerm_apply]
  by_cases hu : u ∈ mins (toPart n σ)
  · rw [ofPartFun_eq_ofMem hu]
    have hEq := congrFun (bwe_perm_mins_to_maxs hσ)
      (((mins (toPart n σ)).orderIsoOfFin (card_mins_eq (toPart n σ))).symm
        ⟨u, hu⟩)
    rw [orderEmb_symm_mins hu] at hEq
    exact hEq.symm
  · rw [ofPartFun_eq_pred hu, ← perm_eq_pred_of_notMem hu]

end MetaMathlibExt
end
