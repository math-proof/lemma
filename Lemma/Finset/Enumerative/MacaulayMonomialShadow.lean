import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MacaulayMonomialShadow
open BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[mms_rep_sum_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_rep_sum_lt (r bound : ℕ) (digits : Fin r → ℕ)
  (hstrict : StrictMono digits) (hlt : ∀ i, digits i < bound) :
  (∑ i, Nat.choose (digits i) (i.1 + 1)) < Nat.choose bound r := by
  induction r generalizing bound with
  | zero => simp
  | succ r ih =>
    let lower : Fin r → ℕ := fun i => digits i.castSucc
    have hlower : StrictMono lower := hstrict.comp Fin.strictMono_castSucc
    have hlowerTop : ∀ i, lower i < digits (Fin.last r) := by
      intro i
      exact hstrict (Fin.castSucc_lt_last i)
    have hlow := ih (digits (Fin.last r)) lower hlower hlowerTop
    have htop : digits (Fin.last r) + 1 ≤ bound := by
      have := hlt (Fin.last r)
      omega
    have hchoose : Nat.choose (digits (Fin.last r) + 1) (r + 1) ≤
      Nat.choose bound (r + 1) := Nat.choose_le_choose (r + 1) htop
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [show digits (Fin.last r) + 1 = (digits (Fin.last r)).succ by omega,
      show r + 1 = r.succ by omega, Nat.choose_succ_succ] at hchoose
    rw [show r.succ = r + 1 by omega] at hchoose
    dsimp [lower] at hlow
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_rep_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_rep_unique (r : ℕ) (f g : Fin r → ℕ) (hf : StrictMono f)
  (hg : StrictMono g)
  (hsum : (∑ i, Nat.choose (f i) (i.1 + 1)) =
    ∑ i, Nat.choose (g i) (i.1 + 1)) : f = g := by
  induction r with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    have htop : f (Fin.last r) = g (Fin.last r) := by
      obtain h | h | h := lt_trichotomy (f (Fin.last r)) (g (Fin.last r))
      · have hbound : ∀ i, f i < g (Fin.last r) := by
        intro i
        exact (hf.monotone (Fin.le_last i)).trans_lt h
        have hlt := mms_rep_sum_lt (r + 1) (g (Fin.last r)) f hf hbound
        rw [hsum, Fin.sum_univ_castSucc] at hlt
        simp only [Fin.val_castSucc, Fin.val_last] at hlt
        omega
      · exact h
      · have hbound : ∀ i, g i < f (Fin.last r) := by
        intro i
        exact (hg.monotone (Fin.le_last i)).trans_lt h
        have hlt := mms_rep_sum_lt (r + 1) (f (Fin.last r)) g hg hbound
        rw [← hsum, Fin.sum_univ_castSucc] at hlt
        simp only [Fin.val_castSucc, Fin.val_last] at hlt
        omega
    let f' : Fin r → ℕ := fun i => f i.castSucc
    let g' : Fin r → ℕ := fun i => g i.castSucc
    have hsum' : (∑ i, Nat.choose (f' i) (i.1 + 1)) =
      ∑ i, Nat.choose (g' i) (i.1 + 1) := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hsum
      simp only [Fin.val_castSucc, Fin.val_last] at hsum
      rw [htop] at hsum
      simpa only [f', g'] using Nat.add_right_cancel hsum
    have hfg' : f' = g' := ih f' g' (hf.comp Fin.strictMono_castSucc)
      (hg.comp Fin.strictMono_castSucc) hsum'
    funext i
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · exact congr_fun hfg' i
    · exact htop

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_shifted_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_shifted_sum_le (r : ℕ) (digits : Fin (r + 1) → ℕ)
  (hstrict : StrictMono digits) :
  (∑ i, Nat.choose (digits i) i.1) ≤
    Nat.choose (digits (Fin.last r) + 1) r := by
  induction r with
  | zero => simp
  | succ r ih =>
    let lower : Fin (r + 1) → ℕ := fun i => digits i.castSucc
    have hlower : StrictMono lower := hstrict.comp Fin.strictMono_castSucc
    have hlow := ih lower hlower
    have hprev : lower (Fin.last r) + 1 ≤ digits (Fin.last (r + 1)) := by
      have := hstrict (Fin.castSucc_lt_last (Fin.last r))
      change digits (Fin.last r).castSucc < digits (Fin.last (r + 1)) at this
      change digits (Fin.last r).castSucc + 1 ≤ digits (Fin.last (r + 1))
      omega
    have hmono : Nat.choose (lower (Fin.last r) + 1) r ≤
      Nat.choose (digits (Fin.last (r + 1))) r := Nat.choose_le_choose r hprev
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hpascal : Nat.choose (digits (Fin.last (r + 1)) + 1) (r + 1) =
      Nat.choose (digits (Fin.last (r + 1))) r +
        Nat.choose (digits (Fin.last (r + 1))) (r + 1) := by
      simpa only [Nat.succ_eq_add_one] using
        Nat.choose_succ_succ (digits (Fin.last (r + 1))) r
    rw [hpascal]
    dsimp [lower] at hlow hmono
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_digits_val_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_digits_val_le (k : ℕ) (digits : Fin (k + 1) → ℕ) (hstrict : StrictMono digits)
  (i : Fin (k + 1)) : i.1 ≤ digits i := by
  have h : ∀ n (hn : n < k + 1), n ≤ digits ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro
      exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have hn' : n < k + 1 := by omega
      have hlt : (⟨n, hn'⟩ : Fin (k + 1)) < ⟨n + 1, hn⟩ :=
        Fin.mk_lt_mk.mpr (by omega)
      have h1 := hstrict hlt
      have h2 := ih hn'
      omega
  exact h i.1 i.2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_lower_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_lower_sum_le (r bound : ℕ) (digits : Fin (r + 1) → ℕ)
  (hstrict : StrictMono digits) (hlt : ∀ i, digits i < bound) :
  (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤
    Nat.choose (bound - 1) r := by
  induction r generalizing bound with
  | zero =>
    by_cases h : digits 0 = 0
    · simp [h]
    · simp [h]
  | succ r ih =>
    let lower : Fin (r + 1) → ℕ := fun i => digits i.castSucc
    have hlower : StrictMono lower := hstrict.comp Fin.strictMono_castSucc
    have hlowerLast : ∀ i, lower i < digits (Fin.last (r + 1)) := by
      intro i
      exact hstrict (Fin.castSucc_lt_last i)
    have hlow := ih (digits (Fin.last (r + 1))) lower hlower hlowerLast
    have hdpos : 0 < digits (Fin.last (r + 1)) := by
      have h := hstrict (Fin.castSucc_lt_last (0 : Fin (r + 1)))
      omega
    have hdle : digits (Fin.last (r + 1)) ≤ bound - 1 := by
      have := hlt (Fin.last (r + 1))
      omega
    have hmono : Nat.choose (digits (Fin.last (r + 1))) (r + 1) ≤
      Nat.choose (bound - 1) (r + 1) := Nat.choose_le_choose (r + 1) hdle
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.ne_of_gt hdpos, ↓reduceIte]
    have hpascal : Nat.choose (digits (Fin.last (r + 1))) (r + 1) =
      Nat.choose (digits (Fin.last (r + 1)) - 1) r +
        Nat.choose (digits (Fin.last (r + 1)) - 1) (r + 1) := by
      have hp := Nat.choose_succ_succ (digits (Fin.last (r + 1)) - 1) r
      have hpred : (digits (Fin.last (r + 1)) - 1).succ =
        digits (Fin.last (r + 1)) := by omega
      rw [hpred] at hp
      simpa only [Nat.succ_eq_add_one] using hp
    rw [hpascal] at hmono
    dsimp [lower] at hlow
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_hockey](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_hockey (base r : ℕ) :
  (∑ i : Fin (r + 1), Nat.choose (base + i.1) i.1) =
    Nat.choose (base + r + 1) r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have hp := Nat.choose_succ_succ (base + r + 1) r
    simpa only [Nat.succ_eq_add_one, add_assoc] using hp.symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_hockey_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_hockey_succ (base r : ℕ) :
  (∑ i : Fin r, Nat.choose (base + i.1) (i.1 + 1)) =
    Nat.choose (base + r) r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have hp := Nat.choose_succ_succ (base + r) r
    have hpos : 0 < Nat.choose (base + r) r := Nat.choose_pos (by omega)
    simp only [Nat.succ_eq_add_one] at hp
    rw [show base + (r + 1) = base + r + 1 by omega]
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_choose_lt_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_choose_lt_succ (k x : ℕ) (hk : 0 < k) (hkx : k ≤ x + 1) :
  Nat.choose x k < Nat.choose (x + 1) k := by
  have hp := Nat.choose_succ_succ x (k - 1)
  have hkpred : (k - 1).succ = k := by omega
  rw [hkpred] at hp
  have hpos : 0 < Nat.choose x (k - 1) := Nat.choose_pos (by omega)
  calc
    Nat.choose x k < Nat.choose x (k - 1) + Nat.choose x k :=
      Nat.lt_add_of_pos_left hpos
    _ = Nat.choose (x + 1) k := by
      simpa only [Nat.succ_eq_add_one] using hp.symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_shifted_lower_max](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_shifted_lower_max (r : ℕ) (digits : Fin (r + 2) → ℕ)
  (hstrict : StrictMono digits)
  (hsum : (∑ i, Nat.choose (digits i) i.1) =
    Nat.choose (digits (Fin.last (r + 1)) + 1) (r + 1)) :
  (∑ i, if i.1 = 0 then 0 else Nat.choose (digits i - 1) (i.1 - 1)) =
    Nat.choose (digits (Fin.last (r + 1))) r := by
  induction r with
  | zero =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    simp
  | succ r ih =>
    let lower : Fin (r + 2) → ℕ := fun i => digits i.castSucc
    have hlower : StrictMono lower := hstrict.comp Fin.strictMono_castSucc
    have hcard : (∑ i, Nat.choose (lower i) i.1) =
      Nat.choose (digits (Fin.last (r + 2))) (r + 1) := by
      change (∑ i, Nat.choose (digits i) i.1) =
        Nat.choose (digits (Fin.last (r + 2)) + 1) (r + 2) at hsum
      rw [Fin.sum_univ_castSucc] at hsum
      simp only [Fin.val_castSucc, Fin.val_last] at hsum
      have hp := Nat.choose_succ_succ (digits (Fin.last (r + 2))) (r + 1)
      simp only [Nat.succ_eq_add_one] at hp
      rw [hp] at hsum
      dsimp [lower]
      exact Nat.add_right_cancel hsum
    have hbound := mms_shifted_sum_le (r + 1) lower hlower
    have hprev : lower (Fin.last (r + 1)) + 1 ≤ digits (Fin.last (r + 2)) := by
      have := hstrict (Fin.castSucc_lt_last (Fin.last (r + 1)))
      change digits (Fin.last (r + 1)).castSucc < digits (Fin.last (r + 2)) at this
      change digits (Fin.last (r + 1)).castSucc + 1 ≤ digits (Fin.last (r + 2))
      omega
    have hmono : Nat.choose (lower (Fin.last (r + 1)) + 1) (r + 1) ≤
      Nat.choose (digits (Fin.last (r + 2))) (r + 1) :=
      Nat.choose_le_choose (r + 1) hprev
    have heq : lower (Fin.last (r + 1)) + 1 = digits (Fin.last (r + 2)) := by
      by_contra! hne
      have hpge : r + 1 ≤ lower (Fin.last (r + 1)) + 1 := by
        have hv := mms_digits_val_le (r + 1) lower hlower (Fin.last (r + 1))
        have hv' : r + 1 ≤ lower (Fin.last (r + 1)) := by
          simpa only [Fin.val_last] using hv
        omega
      have hlt := mms_choose_lt_succ (r + 1) (lower (Fin.last (r + 1)) + 1)
        (by omega) (by omega)
      change Nat.choose (lower (Fin.last (r + 1)) + 1) (r + 1) <
        Nat.choose (lower (Fin.last (r + 1)) + 2) (r + 1) at hlt
      have hmono' : Nat.choose (lower (Fin.last (r + 1)) + 2) (r + 1) ≤
        Nat.choose (digits (Fin.last (r + 2))) (r + 1) :=
        Nat.choose_le_choose (r + 1) (by omega)
      have hchooseEq : Nat.choose (lower (Fin.last (r + 1)) + 1) (r + 1) =
        Nat.choose (digits (Fin.last (r + 2))) (r + 1) := by
        apply Nat.le_antisymm hmono
        rwa [← hcard]
      omega
    have hrec := ih lower hlower (by rw [hcard, heq])
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    simp only [show r + 2 ≠ 0 by omega, ↓reduceIte]
    dsimp [lower] at hrec heq
    have hprevEq : digits (Fin.last (r + 1)).castSucc =
      digits (Fin.last (r + 2)) - 1 := by omega
    rw [hprevEq] at hrec
    change (∑ x : Fin (r + 2), if x.1 = 0 then 0 else
      Nat.choose (digits x.castSucc - 1) (x.1 - 1)) +
        Nat.choose (digits (Fin.last (r + 2)) - 1) (r + 1) =
      Nat.choose (digits (Fin.last (r + 2))) (r + 1)
    have hp := Nat.choose_succ_succ (digits (Fin.last (r + 2)) - 1) r
    have hpred : (digits (Fin.last (r + 2)) - 1).succ =
      digits (Fin.last (r + 2)) := by omega
    rw [hpred] at hp
    simp only [Nat.succ_eq_add_one] at hp
    rwa [hrec]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[shadow_mem_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma shadow_mem_degree (k : ℕ) (A : Finset (ℕ →₀ ℕ)) (b : ℕ →₀ ℕ)
  (hb : b ∈ A.biUnion fun a => a.support.image fun i => a.update i (a i - 1))
  (hdegree : ∀ a ∈ A, a.sum (fun _ e => e) = k + 1) :
  b.sum (fun _ e => e) = k := by
  rw [Finset.mem_biUnion] at hb
  obtain ⟨a, ha, hb⟩ := hb
  rw [Finset.mem_image] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  have hai : a i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hdeg := hdegree a ha
  have hsum := Finsupp.sum_update_add a i (a i - 1) (fun _ e => e) (fun _ => rfl)
    (fun _ _ _ => rfl)
  beta_reduce at hsum
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[shadow_nonempty_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma shadow_nonempty_of_mem (A : Finset (ℕ →₀ ℕ)) (a : ℕ →₀ ℕ) (ha : a ∈ A)
  (hpos : 0 < a.sum (fun _ e => e)) :
  (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).Nonempty := by
  have hsupp : a.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have ha0 : a = 0 := Finsupp.support_eq_empty.mp h
    rw [ha0] at hpos
    simp at hpos
  obtain ⟨i, hi⟩ := hsupp
  exact ⟨_, Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[macaulay_degree_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma macaulay_degree_one (A : Finset (ℕ →₀ ℕ)) (digits : Fin 1 → ℕ)
  (hdegree : ∀ a ∈ A, a.sum (fun _ e => e) = 1)
  (hcard : A.card = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
  (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤
    (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).card := by
  have hterm : ∀ i : Fin 1,
    (if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤ 1 := by
    intro i
    by_cases h : digits i = 0
    · simp [h]
    · simp only [h, ite_false]
      have hi : i.1 = 0 := by
        have h1 := i.2
        omega
      rw [hi, Nat.choose_zero_right]
  have hLHS : (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤ 1 := by
    calc (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1)
      ≤ ∑ _i : Fin 1, 1 := Finset.sum_le_sum fun i _ => hterm i
      _ = 1 := by simp
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    have hpos : 0 < a.sum (fun _ e => e) := by
      rwa [hdegree a ha]
    have hshadow := shadow_nonempty_of_mem A a ha hpos
    have hcardpos :
      0 < (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).card :=
      Finset.card_pos.mpr hshadow
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    subst hA
    have hsum0 : ∑ i : Fin 1, Nat.choose (digits i) (i.1 + 1) = 0 := by
      simpa using hcard.symm
    have hterm0 :
      ∀ i ∈ (Finset.univ : Finset (Fin 1)), Nat.choose (digits i) (i.1 + 1) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hsum0
    have h0 : ∀ i : Fin 1, digits i = 0 := by
      intro i
      have h1 := hterm0 i (Finset.mem_univ i)
      have hi1 : i.1 + 1 = 1 := by
        have h2 := i.2
        omega
      rwa [hi1, Nat.choose_one_right] at h1
    simp [h0]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_raise_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_raise_lower (p : ℕ) (a : ℕ →₀ ℕ) (ha : a p ≠ 0) :
  mms_raise p (mms_lower p a) = a := by
  ext x
  by_cases hx : x = p
  · subst x
    simp [mms_raise, mms_lower]
    omega
  · simp [mms_raise, mms_lower, Finsupp.update_apply, hx]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_lower_raise](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_lower_raise (p : ℕ) (a : ℕ →₀ ℕ) :
  mms_lower p (mms_raise p a) = a := by
  ext x
  by_cases hx : x = p
  · subst x
    simp [mms_raise, mms_lower]
  · simp [mms_raise, mms_lower, Finsupp.update_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_lower_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_lower_inj (p : ℕ) {a b : ℕ →₀ ℕ} (ha : a p ≠ 0) (hb : b p ≠ 0)
  (h : mms_lower p a = mms_lower p b) : a = b := by
  rw [← mms_raise_lower p a ha, ← mms_raise_lower p b hb, h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_raise_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_raise_injective (p : ℕ) : Function.Injective (mms_raise p) := by
  intro a b h
  rw [← mms_lower_raise p a, ← mms_lower_raise p b, h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_raise_lower_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_raise_lower_comm (p q : ℕ) (hpq : q ≠ p) (a : ℕ →₀ ℕ)
  (ha : a p ≠ 0) : mms_raise p (mms_lower q (mms_lower p a)) = mms_lower q a := by
  ext x
  by_cases hxp : x = p
  · subst x
    simp [mms_raise, mms_lower, Finsupp.update_apply, hpq, Ne.symm hpq]
    omega
  · by_cases hxq : x = q
    · subst x
      simp [mms_raise, mms_lower, Finsupp.update_apply, hpq, Ne.symm hpq]
    · simp [mms_raise, mms_lower, Finsupp.update_apply, hxp, hxq]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_shadow_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_shadow_mono {A C : Finset (ℕ →₀ ℕ)} (hCA : C ⊆ A) :
  mms_shadow C ⊆ mms_shadow A := by
  intro x hx
  rw [mms_shadow, Finset.mem_biUnion] at hx ⊢
  obtain ⟨a, ha, hx⟩ := hx
  exact ⟨a, hCA ha, hx⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_shadow_coord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_shadow_coord_zero (p : ℕ) (C : Finset (ℕ →₀ ℕ))
  (hzero : ∀ a ∈ C, a p = 0) {x : ℕ →₀ ℕ} (hx : x ∈ mms_shadow C) : x p = 0 := by
  rw [mms_shadow, Finset.mem_biUnion] at hx
  obtain ⟨a, ha, hx⟩ := hx
  rw [Finset.mem_image] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have hqp : q ≠ p := by
    intro h
    subst q
    exact Finsupp.mem_support_iff.mp hq (hzero a ha)
  simp [mms_lower, Finsupp.update_apply, Ne.symm hqp, hzero a ha]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mms_raise_shadow_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma mms_raise_shadow_subset (p : ℕ) (A P : Finset (ℕ →₀ ℕ))
  (hPA : P ⊆ A) (hpos : ∀ a ∈ P, a p ≠ 0) :
  (mms_shadow (P.image (mms_lower p))).image (mms_raise p) ⊆ mms_shadow A := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [mms_shadow, Finset.mem_biUnion] at hc
  obtain ⟨b, hb, hc⟩ := hc
  rw [Finset.mem_image] at hb hc
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨q, hq, rfl⟩ := hc
  rw [mms_shadow, Finset.mem_biUnion]
  by_cases hqp : q = p
  · subst q
    have hlop : mms_lower p a p ≠ 0 := Finsupp.mem_support_iff.mp hq
    refine ⟨a, hPA ha, Finset.mem_image.mpr ⟨p, ?_, ?_⟩⟩
    · exact Finsupp.mem_support_iff.mpr (hpos a ha)
    · rw [mms_raise_lower p (mms_lower p a) hlop]
  · refine ⟨a, hPA ha, Finset.mem_image.mpr ⟨q, ?_, ?_⟩⟩
    · have haq : mms_lower p a q = a q := by
      simp only [mms_lower, Finsupp.update_apply]
      split
      · rename_i h
        exact (hqp h).elim
      · rfl
      exact Finsupp.mem_support_iff.mpr (by
        rw [← haq]
        exact Finsupp.mem_support_iff.mp hq)
    · exact (mms_raise_lower_comm p q hqp a (hpos a ha)).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[macaulay_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma macaulay_empty (k : ℕ) (digits : Fin (k + 1) → ℕ)
  (hstrict : StrictMono digits)
  (hcard : (0 : ℕ) = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
  (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) = 0 := by
  have hsum0 : ∑ i : Fin (k + 1), Nat.choose (digits i) (i.1 + 1) = 0 := hcard.symm
  have hterm0 : ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))),
    Nat.choose (digits i) (i.1 + 1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hsum0
  have hdig : ∀ i : Fin (k + 1), digits i = i.1 := by
    intro i
    have h1 := hterm0 i (Finset.mem_univ i)
    have hle : digits i ≤ i.1 := by
      by_contra hcon
      have hlt : i.1 < digits i := Nat.lt_of_not_ge hcon
      have hpos : 0 < Nat.choose (digits i) (i.1 + 1) :=
        Nat.choose_pos (by omega)
      omega
    have hge : i.1 ≤ digits i := mms_digits_val_le k digits hstrict i
    omega
  apply Finset.sum_eq_zero
  intro i _
  rw [hdig i]
  by_cases hi : i.1 = 0
  · simp [hi]
  · simp only [hi, ite_false]
    exact Nat.choose_eq_zero_of_lt (by omega)

end MetaMathlibExt

/--
[macaulay_multiset_shadow_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma macaulay_multiset_shadow_minimal_eq
  {k : ℕ}
  {A : Finset (ℕ →₀ ℕ)}
  {digits : Fin (k + 1) → ℕ}
-- given
  (hdegree : ∀ a ∈ A, a.sum (fun _ e => e) = k + 1)
  (hstrict : StrictMono digits)
  (hcard : A.card = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
-- imply
  (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤
    (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).card := by
-- proof
  apply MetaMathlibExt.macaulay_multiset_shadow_minimal k A digits hdegree hstrict hcard


-- created on 2026-10-20
-- updated on 2026-10-23
