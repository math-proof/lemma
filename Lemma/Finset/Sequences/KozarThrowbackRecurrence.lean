import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Sequences.KozarThrowbackRecurrence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[tbStep_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma tbStep_injective (Y : ℕ → ℕ) (hY : Function.Injective Y) :
  Function.Injective (tbStep Y) := by
  intro a b hab
  unfold tbStep at hab
  by_cases ha : a < Y 0
  · by_cases hb : b < Y 0
    · rw [ite_eq_left ha, ite_eq_left hb] at hab
      have h := hY hab
      omega
    · by_cases hb' : b = Y 0
      · rw [ite_eq_left ha, ite_eq_right hb, ite_eq_left hb'] at hab
        have h := hY hab
        omega
      · rw [ite_eq_left ha, ite_eq_right hb, ite_eq_right hb'] at hab
        have h := hY hab
        omega
  · by_cases ha' : a = Y 0
    · by_cases hb : b < Y 0
      · rw [ite_eq_right ha, ite_eq_left ha', ite_eq_left hb] at hab
        have h := hY hab
        omega
      · by_cases hb' : b = Y 0
        · rw [ite_eq_right ha, ite_eq_left ha', ite_eq_right hb, ite_eq_left hb'] at hab
          omega
        · rw [ite_eq_right ha, ite_eq_left ha', ite_eq_right hb, ite_eq_right hb'] at hab
          have h := hY hab
          omega
    · by_cases hb : b < Y 0
      · rw [ite_eq_right ha, ite_eq_right ha', ite_eq_left hb] at hab
        have h := hY hab
        omega
      · by_cases hb' : b = Y 0
        · rw [ite_eq_right ha, ite_eq_right ha', ite_eq_right hb, ite_eq_left hb'] at hab
          have h := hY hab
          omega
        · rw [ite_eq_right ha, ite_eq_right ha', ite_eq_right hb, ite_eq_right hb'] at hab
          have h := hY hab
          omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tbStep_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma tbStep_mem (Y : ℕ → ℕ) (i : ℕ) : ∃ j, tbStep Y i = Y j := by
  unfold tbStep
  by_cases h : i < Y 0
  · exact ⟨i + 1, by rw [ite_eq_left h]⟩
  · by_cases h2 : i = Y 0
    · exact ⟨0, by rw [ite_eq_right h, ite_eq_left h2]⟩
    · exact ⟨i, by rw [ite_eq_right h, ite_eq_right h2]⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tbStep_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma tbStep_preimage (Y : ℕ → ℕ) (p : ℕ) : ∃ p', tbStep Y p' = Y p := by
  by_cases hp : p = 0
  · subst hp
    refine ⟨Y 0, ?_⟩
    unfold tbStep
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
  · have hp1 : 1 ≤ p := by omega
    by_cases h : p - 1 < Y 0
    · refine ⟨p - 1, ?_⟩
      unfold tbStep
      rw [ite_eq_left h]
      have hpp : p - 1 + 1 = p := by omega
      rw [hpp]
    · refine ⟨p, ?_⟩
      unfold tbStep
      have h1 : ¬ p < Y 0 := by omega
      have h2 : ¬ p = Y 0 := by omega
      rw [ite_eq_right h1, ite_eq_right h2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tb_iterate_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma tb_iterate_comm (k : ℕ) (Y : ℕ → ℕ) :
  Nat.iterate tbStep k (tbStep Y) = tbStep (Nat.iterate tbStep k Y) := by
  induction k generalizing Y with
  | zero => rfl
  | succ k ih => exact ih (tbStep Y)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Yseq_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma Yseq_succ (k : ℕ) (i : ℕ) : Yseq (k + 1) i = tbStep (Yseq k) i := by
  unfold Yseq
  have h1 : Nat.iterate tbStep (k + 1) tbX = Nat.iterate tbStep k (tbStep tbX) := rfl
  have h2 : Nat.iterate tbStep k (tbStep tbX) = tbStep (Nat.iterate tbStep k tbX) :=
    tb_iterate_comm k tbX
  rw [h1, h2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tbX_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma tbX_injective : Function.Injective tbX := by
  intro a b hab
  unfold tbX at hab
  simp at hab
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[three_le_tbX](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma three_le_tbX (i : ℕ) : 3 ≤ tbX i := by
  unfold tbX
  show 3 ≤ i + 3
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[three_le_Yseq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma three_le_Yseq (k : ℕ) (i : ℕ) : 3 ≤ Yseq k i := by
  induction k generalizing i with
  | zero => exact three_le_tbX i
  | succ k ih =>
    rw [Yseq_succ]
    obtain ⟨j, hj⟩ := tbStep_mem (Yseq k) i
    rw [hj]
    exact ih j

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Yseq_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma Yseq_injective (k : ℕ) : Function.Injective (Yseq k) := by
  induction k with
  | zero => exact tbX_injective
  | succ k ih =>
    have hY : Yseq (k + 1) = tbStep (Yseq k) := by
      funext i
      exact Yseq_succ k i
    rw [hY]
    exact tbStep_injective (Yseq k) ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Yseq_pos_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma Yseq_pos_exists (k : ℕ) (v : ℕ) (hv : 3 ≤ v) : ∃ p, Yseq k p = v := by
  have hj : tbX (v - 3) = v := by
    unfold tbX
    show v - 3 + 3 = v
    omega
  induction k with
  | zero => exact ⟨v - 3, hj⟩
  | succ k ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨p', hp'⟩ := tbStep_preimage (Yseq k) p
    refine ⟨p', ?_⟩
    have hY : Yseq (k + 1) = tbStep (Yseq k) := by
      funext i
      exact Yseq_succ k i
    rw [hY, hp', hp]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tbStep_fwd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma tbStep_fwd (Y : ℕ → ℕ) (p : ℕ) (hp : 1 ≤ p) (h : p - 1 < Y 0) :
  tbStep Y (p - 1) = Y p := by
  unfold tbStep
  rw [ite_eq_left h]
  have hpp : p - 1 + 1 = p := by omega
  rw [hpp]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tbStep_fwd_stay](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma tbStep_fwd_stay (Y : ℕ → ℕ) (p : ℕ) (hp : 1 ≤ p) (h : ¬ p - 1 < Y 0) :
  tbStep Y p = Y p := by
  unfold tbStep
  have h1 : ¬ p < Y 0 := by omega
  have h2 : ¬ p = Y 0 := by omega
  rw [ite_eq_right h1, ite_eq_right h2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma key (p : ℕ) :
  ∀ (k0 : ℕ) (v : ℕ), 3 ≤ v → Yseq k0 p = v → ∃ k, k0 ≤ k ∧ Yseq k 0 = v := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro k0 v hv hpos
    by_cases hp0 : p = 0
    · subst hp0
      exact ⟨k0, le_rfl, hpos⟩
    · by_contra hcon
      push Not at hcon
      classical
      have hex : ∀ k, ∃ q, Yseq k q = v := fun k => Yseq_pos_exists k v hv
      have hpos_ge : ∀ k, k0 ≤ k → 1 ≤ Nat.find (hex k) := by
        intro k hk
        by_cases h0 : Nat.find (hex k) = 0
        · have hY0 : Yseq k 0 = v := by
          rw [← h0]
          exact Nat.find_spec (hex k)
          exact absurd hY0 (hcon k hk)
        · omega
      have hmono : ∀ k, k0 ≤ k → Nat.find (hex (k + 1)) ≤ Nat.find (hex k) := by
        intro k hk
        have hm := Nat.find_spec (hex k)
        have hge := hpos_ge k hk
        by_cases hlt : Nat.find (hex k) - 1 < Yseq k 0
        · have hq : Yseq (k + 1) (Nat.find (hex k) - 1) = v := by
          rw [Yseq_succ k (Nat.find (hex k) - 1),
            tbStep_fwd (Yseq k) (Nat.find (hex k)) hge hlt, hm]
          exact le_trans (Nat.find_le hq) (Nat.sub_le _ _)
        · have hq : Yseq (k + 1) (Nat.find (hex k)) = v := by
          rw [Yseq_succ k (Nat.find (hex k)),
            tbStep_fwd_stay (Yseq k) (Nat.find (hex k)) hge hlt, hm]
          exact Nat.find_le hq
      have hmono_le : ∀ k1 k2, k0 ≤ k1 → k1 ≤ k2 → Nat.find (hex k2) ≤ Nat.find (hex k1) := by
        intro k1 k2 hk1 hk12
        have hP : ∀ n, k1 ≤ n → Nat.find (hex n) ≤ Nat.find (hex k1) := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => exact le_rfl
          | succ n hmn ih2 => exact le_trans (hmono n (le_trans hk1 hmn)) ih2
        exact hP k2 hk12
      have hset : ∃ m, ∃ k, k0 ≤ k ∧ Nat.find (hex k) = m :=
        ⟨Nat.find (hex k0), k0, le_rfl, rfl⟩
      set mstar := Nat.find hset with hmstar_def
      have hspec_star : ∃ k, k0 ≤ k ∧ Nat.find (hex k) = mstar := Nat.find_spec hset
      have hmin : ∀ m, (∃ k, k0 ≤ k ∧ Nat.find (hex k) = m) → mstar ≤ m := by
        intro m hm
        exact Nat.find_min' hset hm
      obtain ⟨K', hK'0, hK'star⟩ := hspec_star
      have hstar_ge : 1 ≤ mstar := by
        rw [← hK'star]
        exact hpos_ge K' hK'0
      have hstab : ∀ k, K' ≤ k → Nat.find (hex k) = mstar := by
        intro k hK'k
        have hk0 : k0 ≤ k := le_trans hK'0 hK'k
        have h1 : Nat.find (hex k) ≤ mstar := by
          rw [← hK'star]
          exact hmono_le K' k hK'0 hK'k
        have h2 : mstar ≤ Nat.find (hex k) := hmin _ ⟨k, hk0, rfl⟩
        omega
      have hlead : ∀ k, K' ≤ k → Yseq k 0 < mstar := by
        intro k hk
        have hk0 : k0 ≤ k := le_trans hK'0 hk
        have hK1 : K' ≤ k + 1 := le_trans hk (Nat.le_succ k)
        have e1 : Nat.find (hex (k + 1)) = mstar := hstab (k + 1) hK1
        have e0 : Nat.find (hex k) = mstar := hstab k hk
        have hge : 1 ≤ Nat.find (hex k) := hpos_ge k hk0
        by_contra hcon2
        push Not at hcon2
        have hlt : Nat.find (hex k) - 1 < Yseq k 0 := by
          rw [e0]
          omega
        have hq : Yseq (k + 1) (Nat.find (hex k) - 1) = v := by
          rw [Yseq_succ k (Nat.find (hex k) - 1),
            tbStep_fwd (Yseq k) (Nat.find (hex k)) hge hlt, Nat.find_spec (hex k)]
        have hle2 : Nat.find (hex (k + 1)) ≤ Nat.find (hex k) - 1 := Nat.find_le hq
        omega
      have hpig : ∃ i, i < mstar ∧ mstar ≤ Yseq K' i := by
        by_contra hnone
        push Not at hnone
        have hmem : Finset.image (Yseq K') (Finset.range mstar) ⊆ Finset.Ico 3 mstar := by
          intro y hy
          rw [Finset.mem_image] at hy
          obtain ⟨i, hi, rfl⟩ := hy
          rw [Finset.mem_range] at hi
          rw [Finset.mem_Ico]
          exact ⟨three_le_Yseq K' i, hnone i hi⟩
        have hcard_img : (Finset.image (Yseq K') (Finset.range mstar)).card = mstar := by
          rw [Finset.card_image_of_injOn]
          · exact Finset.card_range mstar
          · intro a ha b hb hab
            rw [Finset.mem_coe, Finset.mem_range] at ha hb
            exact Yseq_injective K' hab
        have hcard_ico : (Finset.Ico 3 mstar).card = mstar - 3 := Nat.card_Ico 3 mstar
        have hle_card := Finset.card_le_card hmem
        rw [hcard_img, hcard_ico] at hle_card
        omega
      obtain ⟨i, hi_lt, hi_ge⟩ := hpig
      have hi3 : 3 ≤ Yseq K' i := three_le_Yseq K' i
      have hstar_le_p : mstar ≤ p := by
        have h1 : Nat.find (hex K') ≤ Nat.find (hex k0) := hmono_le k0 K' le_rfl hK'0
        have h2 : Nat.find (hex k0) ≤ p := Nat.find_le hpos
        rw [hK'star] at h1
        omega
      have hilt_p : i < p := by omega
      obtain ⟨k, hkK', hk0eq⟩ := ih i hilt_p K' (Yseq K' i) hi3 rfl
      have hklead : Yseq k 0 < mstar := hlead k hkK'
      omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[kozar_throwback_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
lemma kozar_throwback_recurrence
  :
-- imply
  let throwbackStep : (ℕ → ℕ) → (ℕ → ℕ) := by
-- proof
  intro throwbackStep X T n hn N
  obtain ⟨p, hp⟩ := Yseq_pos_exists N n hn
  obtain ⟨k, hkN, hk_eq⟩ := key p N n hn hp
  exact ⟨k, hkN, hk_eq⟩
end



-- created on 2026-10-20
-- updated on 2026-10-26
