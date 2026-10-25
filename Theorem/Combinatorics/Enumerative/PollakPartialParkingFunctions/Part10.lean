/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part9


namespace MetaMathlibExt.PollakPartialParking

theorem emb_val (t : ℕ) (x : Fin t) : (emb t x).val = x.val :=
  ZMod.val_natCast_of_lt (by have := x.isLt; omega)

theorem extra_val (t : ℕ) : (extra t).val = t :=
  ZMod.val_natCast_of_lt (Nat.lt_succ_self t)

theorem emb_injective (t : ℕ) : Function.Injective (emb t) := by
  intro x y hxy
  have h := congrArg ZMod.val hxy
  rw [emb_val, emb_val] at h
  exact Fin.ext h

theorem emb_ne_extra (t : ℕ) (x : Fin t) : emb t x ≠ extra t := by
  intro hcon
  have h := congrArg ZMod.val hcon
  rw [emb_val, extra_val] at h
  omega

/-- Circle parking from a linear-range spot finds the linear take. -/
theorem bridge_some (t : ℕ) (ol : Finset (Fin t)) (a b : Fin t)
    (occ : Finset (ZMod (t + 1))) (himg : occ = ol.image (emb t))
    (hc : occ.card < t + 1)
    (hff : linFirstFree t ol a.val = some b) :
    firstFree t occ (emb t a) hc = emb t b := by
  have hmem := linFirstFree_mem t ol a.val b hff
  have hle_ab : a.val ≤ b.val := hmem.1
  have hbn : b ∉ ol := hmem.2
  have hQ : ∃ j : ℕ, emb t a + ((j : ℕ) : ZMod (t + 1)) ∉ occ :=
    ray_free_exists t occ (emb t a) hc
  set d := b.val - a.val with hd
  have hray : emb t a + ((d : ℕ) : ZMod (t + 1)) = emb t b := by
    unfold emb
    rw [← Nat.cast_add]
    congr 1
    omega
  have hmem_at : ∀ j : ℕ, j < d → emb t a + ((j : ℕ) : ZMod (t + 1)) ∈ occ := by
    intro j hj
    have hjlt : a.val + j < t := by
      have hblt := b.isLt
      omega
    have hmem_ol : (⟨a.val + j, hjlt⟩ : Fin t) ∈ ol := by
      by_contra hcon
      have hle := linFirstFree_le t ol a.val b hff _ (Nat.le_add_right _ _) hcon
      have hle' : b.val ≤ a.val + j := hle
      omega
    have hray_j : emb t a + ((j : ℕ) : ZMod (t + 1)) =
        emb t (⟨a.val + j, hjlt⟩ : Fin t) := by
      unfold emb
      rw [← Nat.cast_add]
    rw [hray_j, himg, Finset.mem_image]
    exact ⟨_, hmem_ol, rfl⟩
  have hfind : Nat.find hQ = d := by
    apply le_antisymm
    · apply Nat.find_min' hQ
      rw [hray, himg]
      intro hcon
      rw [Finset.mem_image] at hcon
      obtain ⟨y, hy, hye⟩ := hcon
      have heq : y = b := emb_injective t hye
      rw [heq] at hy
      exact hbn hy
    · by_contra hcon
      have hlt : Nat.find hQ < d := lt_of_not_ge hcon
      exact (Nat.find_spec hQ) (hmem_at _ hlt)
  have hfirst : firstFree t occ (emb t a) hc =
      emb t a + (((Nat.find hQ : ℕ)) : ZMod (t + 1)) := rfl
  rw [hfirst, hfind, hray]

/-- Circle parking fails into the extra spot exactly when linear parking fails. -/
theorem bridge_none (t : ℕ) (ol : Finset (Fin t)) (a : Fin t)
    (occ : Finset (ZMod (t + 1))) (himg : occ = ol.image (emb t))
    (hc : occ.card < t + 1) (hce : extra t ∉ occ)
    (hff : linFirstFree t ol a.val = none) :
    firstFree t occ (emb t a) hc = extra t := by
  have hQ : ∃ j : ℕ, emb t a + ((j : ℕ) : ZMod (t + 1)) ∉ occ :=
    ray_free_exists t occ (emb t a) hc
  set d := t - a.val with hd
  have hmem_at : ∀ j : ℕ, j < d → emb t a + ((j : ℕ) : ZMod (t + 1)) ∈ occ := by
    intro j hj
    have hjlt : a.val + j < t := by
      have halt := a.isLt
      omega
    have hmem_ol : (⟨a.val + j, hjlt⟩ : Fin t) ∈ ol :=
      linFirstFree_none t ol a.val hff _ (Nat.le_add_right _ _)
    have hray_j : emb t a + ((j : ℕ) : ZMod (t + 1)) =
        emb t (⟨a.val + j, hjlt⟩ : Fin t) := by
      unfold emb
      rw [← Nat.cast_add]
    rw [hray_j, himg, Finset.mem_image]
    exact ⟨_, hmem_ol, rfl⟩
  have hray_d : emb t a + ((d : ℕ) : ZMod (t + 1)) = extra t := by
    unfold emb extra
    rw [← Nat.cast_add]
    congr 1
    have halt := a.isLt
    omega
  have hQd : emb t a + ((d : ℕ) : ZMod (t + 1)) ∉ occ := by
    rwa [hray_d]
  have hfind : Nat.find hQ = d := by
    apply le_antisymm
    · exact Nat.find_min' hQ hQd
    · by_contra hcon
      have hlt : Nat.find hQ < d := lt_of_not_ge hcon
      exact (Nat.find_spec hQ) (hmem_at _ hlt)
  have hfirst : firstFree t occ (emb t a) hc =
      emb t a + (((Nat.find hQ : ℕ)) : ZMod (t + 1)) := rfl
  rw [hfirst, hfind, hray_d]

/-- Circle-occupied card bound. -/
theorem circle_card_lt (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (m : ℕ) (hm : m ≤ s) : (parkOcc s t g hst m).card < t + 1 := by
  have hle := card_parkOcc_le s t g hst m
  omega

/-- Empty extra spot implies linear success. -/
theorem circle_empty_imp_linSuccess (s t : ℕ) (f : Fin s → Fin t)
    (hst : s ≤ t)
    (hmem : extra t ∈ parkEmpty s t (lift s t f) hst) :
    LinSuccess s t f := by
  have hnot : extra t ∉ parkOcc s t (lift s t f) hst s := by
    have h := hmem
    unfold parkEmpty at h
    exact (Finset.mem_sdiff.mp h).2
  have key : ∀ m : ℕ, m ≤ s → ∃ ol : { occ : Finset (Fin t) // occ.card ≤ m },
      linOccAux s t f m = some ol ∧
        parkOcc s t (lift s t f) hst m = ol.val.image (emb t) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨⟨∅, by simp⟩, linOccAux_zero s t f, ?_⟩
      change parkOcc s t (lift s t f) hst 0 = (∅ : Finset (Fin t)).image (emb t)
      simp only [parkOcc, parkOccAux, Finset.image_empty]
    | succ m ih =>
      intro hms1
      have hms : m ≤ s := by omega
      obtain ⟨ol, hol, hcir⟩ := ih hms
      have hmlt : m < s := by omega
      match hff : linFirstFree t ol.val (f ⟨m, hmlt⟩).val with
      | none =>
        exfalso
        have hcard := circle_card_lt s t (lift s t f) hst m (by omega)
        have hsub := parkOcc_mono s t (lift s t f) hst (by omega : m ≤ s)
        have hce : extra t ∉ parkOcc s t (lift s t f) hst m :=
          fun hcon => hnot (hsub hcon)
        have hbridge := bridge_none t ol.val (f ⟨m, hmlt⟩)
          (parkOcc s t (lift s t f) hst m) hcir hcard hce hff
        have hstep := parkOcc_succ_of_lt s t (lift s t f) hst m hmlt
        have hass : parkAssign s t (lift s t f) hst m hmlt = extra t :=
          hbridge
        have hmem1 : extra t ∈ parkOcc s t (lift s t f) hst (m + 1) := by
          rw [hstep, hass]
          exact Finset.mem_insert_self _ _
        have hsub2 := parkOcc_mono s t (lift s t f) hst (by omega : m + 1 ≤ s)
        exact hnot (hsub2 hmem1)
      | some b =>
        have hsucc2 := linOccAux_succ_some s t f m ol hol hmlt b hff
        have hcard := circle_card_lt s t (lift s t f) hst m (by omega)
        have hbridge := bridge_some t ol.val (f ⟨m, hmlt⟩) b
          (parkOcc s t (lift s t f) hst m) hcir hcard hff
        have hass : parkAssign s t (lift s t f) hst m hmlt = emb t b :=
          hbridge
        refine ⟨⟨insert b ol.val, ?_⟩, hsucc2, ?_⟩
        · have hle := ol.property
          have hmem := linFirstFree_mem t ol.val (f ⟨m, hmlt⟩).val b hff
          have hci := Finset.card_insert_le b ol.val
          omega
        · rw [parkOcc_succ_of_lt s t (lift s t f) hst m hmlt, hass,
            Finset.image_insert, hcir]
  obtain ⟨ol, hol, _⟩ := key s (le_refl s)
  unfold LinSuccess
  exact hol.symm ▸ Option.isSome_some

/-- Linear success keeps the extra spot empty. -/
theorem linSuccess_imp_circle_empty (s t : ℕ) (f : Fin s → Fin t)
    (hst : s ≤ t) (hsucc : LinSuccess s t f) :
    extra t ∈ parkEmpty s t (lift s t f) hst := by
  have key : ∀ m : ℕ, m ≤ s → ∃ ol : { occ : Finset (Fin t) // occ.card ≤ m },
      linOccAux s t f m = some ol ∧
        parkOcc s t (lift s t f) hst m = ol.val.image (emb t) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨⟨∅, by simp⟩, linOccAux_zero s t f, ?_⟩
      change parkOcc s t (lift s t f) hst 0 = (∅ : Finset (Fin t)).image (emb t)
      simp only [parkOcc, parkOccAux, Finset.image_empty]
    | succ m ih =>
      intro hms1
      have hms : m ≤ s := by omega
      obtain ⟨ol, hol, hcir⟩ := ih hms
      have hmlt : m < s := by omega
      obtain ⟨b, hb⟩ := linTake_some_of_success s t f hsucc m hmlt
      have hff : linFirstFree t ol.val (f ⟨m, hmlt⟩).val = some b := by
        have h1 : linTake s t f m hmlt = linFirstFree t ol.val (f ⟨m, hmlt⟩).val :=
          linTake_eq s t f m hmlt ol hol
        rwa [h1] at hb
      have hsucc2 := linOccAux_succ_some s t f m ol hol hmlt b hff
      have hcard := circle_card_lt s t (lift s t f) hst m (by omega)
      have hbridge := bridge_some t ol.val (f ⟨m, hmlt⟩) b
        (parkOcc s t (lift s t f) hst m) hcir hcard hff
      have hass : parkAssign s t (lift s t f) hst m hmlt = emb t b :=
        hbridge
      refine ⟨⟨insert b ol.val, ?_⟩, hsucc2, ?_⟩
      · have hle := ol.property
        have hmem := linFirstFree_mem t ol.val (f ⟨m, hmlt⟩).val b hff
        have hci := Finset.card_insert_le b ol.val
        omega
      · rw [parkOcc_succ_of_lt s t (lift s t f) hst m hmlt, hass,
          Finset.image_insert, hcir]
  obtain ⟨ol, hol, hcir⟩ := key s (le_refl s)
  have hne : extra t ∉ ol.val.image (emb t) := by
    intro hcon
    rw [Finset.mem_image] at hcon
    obtain ⟨y, _, hye⟩ := hcon
    exact emb_ne_extra t y hye
  rw [← hcir] at hne
  change extra t ∈ Finset.univ \ parkOcc s t (lift s t f) hst s
  rw [Finset.mem_sdiff]
  exact ⟨Finset.mem_univ _, hne⟩

/-- A circle function leaving the extra spot empty never prefers it. -/
theorem circle_empty_avoids (s t : ℕ) (g : Fin s → ZMod (t + 1))
    (hst : s ≤ t) (hmem : extra t ∈ parkEmpty s t g hst)
    (i : Fin s) : g i ≠ extra t := by
  have hmemE : extra t ∉ parkOcc s t g hst s := by
    have h := hmem
    unfold parkEmpty at h
    exact (Finset.mem_sdiff.mp h).2
  intro hcon
  by_cases h : extra t ∈ parkOcc s t g hst i.val
  · exact hmemE (parkOcc_mono s t g hst (by have := i.isLt; omega) h)
  · have hcard : (parkOcc s t g hst i.val).card < t + 1 :=
      circle_card_lt s t g hst i.val (by have := i.isLt; omega)
    have hQ0 : extra t + ((0 : ℕ) : ZMod (t + 1)) ∉ parkOcc s t g hst i.val := by
      simpa using h
    have hfind : Nat.find (ray_free_exists t (parkOcc s t g hst i.val) (extra t) hcard) = 0 :=
      Nat.le_zero.mp (Nat.find_min' _ hQ0)
    have hass : parkAssign s t g hst i.val i.isLt = extra t := by
      have hgi : g ⟨i.val, i.isLt⟩ = extra t := hcon
      have hbase : firstFree t (parkOcc s t g hst i.val) (extra t) hcard = extra t := by
        have hfirst : firstFree t (parkOcc s t g hst i.val) (extra t) hcard =
            extra t + (((Nat.find (ray_free_exists t (parkOcc s t g hst i.val) (extra t) hcard) :
                ℕ)) : ZMod (t + 1)) := rfl
        rw [hfirst, hfind]
        simp
      unfold parkAssign
      rw [hgi]
      exact hbase
    have hmem1 : extra t ∈ parkOcc s t g hst (i.val + 1) := by
      rw [parkOcc_succ_of_lt s t g hst i.val i.isLt, hass]
      exact Finset.mem_insert_self _ _
    exact hmemE (parkOcc_mono s t g hst (by have := i.isLt; omega) hmem1)

end MetaMathlibExt.PollakPartialParking
