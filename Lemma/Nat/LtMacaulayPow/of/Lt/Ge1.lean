import Mathlib
import sympy.Basic
import Def.Nat_MacaulayPow
open Nat


/-- ported from external source -/

noncomputable def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

private lemma  macaulayPow_succ (d a : ℕ) :
  macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + macaulayPow d (a - (top d a).choose (d + 1)) := by
  rw [macaulayPow, top]

private lemma  succ_le_choose (d j : ℕ) : j + 1 ≤ (j + d + 1).choose (d + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (j + 1 + d + 1).choose (d + 1) = (j + d + 1).choose d + (j + d + 1).choose (d + 1) := by
      rw [show j + 1 + d + 1 = (j + d + 1) + 1 by ring, Nat.choose_succ_succ]
    have h2 : 1 ≤ (j + d + 1).choose d := Nat.choose_pos (by omega)
    omega

private lemma  le_bound {d a k : ℕ} (h : k.choose (d + 1) ≤ a) : k ≤ a + d + 1 := by
  by_cases hk : k ≤ d
  · omega
  ·
    obtain ⟨j, rfl⟩ : ∃ j, k = j + d + 1 := ⟨k - (d + 1), by omega⟩
    have := succ_le_choose d j
    omega

private lemma  choose_le_iff (d a k : ℕ) : k.choose (d + 1) ≤ a ↔ k ≤ top d a := by
  constructor
  ·
    intro h
    exact Nat.le_findGreatest (le_bound h) h
  ·
    intro h
    have hspec : (top d a).choose (d + 1) ≤ a :=
      Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (m := 0) (Nat.zero_le _) (by simp)
    refine (Nat.choose_le_choose (d + 1) h).trans hspec

private lemma  top_choose_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a := (choose_le_iff d a _).2 le_rfl

private lemma  lt_succ_top_choose (d a : ℕ) : a < (top d a + 1).choose (d + 1) := by
  by_contra h
  have := (choose_le_iff d a (top d a + 1)).1 (not_lt.1 h)
  omega

private lemma  top_eq {d a k : ℕ} (h₁ : k.choose (d + 1) ≤ a) (h₂ : a < (k + 1).choose (d + 1)) : top d a = k := by
  have hk : k ≤ top d a := (choose_le_iff d a k).1 h₁
  rcases hk.lt_or_eq with hlt | heq
  · exact absurd ((choose_le_iff d a (k + 1)).2 (by omega)) (not_le.2 h₂)
  · exact heq.symm

private lemma  top_mono (d : ℕ) {a b : ℕ} (h : a ≤ b) : top d a ≤ top d b :=
  (choose_le_iff d b _).1 ((top_choose_le d a).trans h)

private lemma  macaulayPow_zero_right (d : ℕ) : macaulayPow d 0 = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have ht : top d 0 = d := top_eq (by simp [Nat.choose_succ_self]) (by simp)
    rw [macaulayPow_succ, ht, Nat.choose_succ_self, Nat.choose_succ_self, Nat.sub_zero, ih]

private lemma  macaulayPow_succ_choose (d K : ℕ) (hK : d ≤ K) :
  macaulayPow (d + 1) (K.choose (d + 1)) = (K + 1).choose (d + 2) := by
  have ht : top d (K.choose (d + 1)) = K := by
    refine top_eq le_rfl ?_
    rw [Nat.choose_succ_succ']
    have : 0 < K.choose d := Nat.choose_pos hK
    omega
  rw [macaulayPow_succ, ht, Nat.sub_self, macaulayPow_zero_right, Nat.add_zero]

private lemma  macaulayPow_one (a : ℕ) : macaulayPow 1 a = (a + 1).choose 2 := by
  have ht : top 0 a = a := top_eq (by simp) (by simp)
  rw [macaulayPow_succ, ht]
  simp [macaulayPow]

private lemma  strictMono_succ (d : ℕ) : ∀ a b : ℕ, a < b → macaulayPow (d + 1) a < macaulayPow (d + 1) b := by
  induction d with
  | zero =>
    intro a b hab
    rw [macaulayPow_one, macaulayPow_one]
    have h1 : (a + 1).choose 2 < (a + 2).choose 2 := by
      rw [show a + 2 = (a + 1) + 1 by ring, Nat.choose_succ_succ (a + 1) 1]
      simp
    refine h1.trans_le (Nat.choose_le_choose 2 (by omega))
  | succ d ih =>
    intro a b hab
    rw [macaulayPow_succ (d + 1) a, macaulayPow_succ (d + 1) b]
    have e1 : d + 1 + 1 = d + 2 := rfl
    have e2 : d + 1 + 2 = d + 3 := rfl
    simp only [e1, e2]
    have hka := top_choose_le (d + 1) a
    have hkb := top_choose_le (d + 1) b
    simp only [e1] at hka hkb
    have hmono : top (d + 1) a ≤ top (d + 1) b := top_mono (d + 1) hab.le
    rcases hmono.lt_or_eq with hlt | heq
    ·
      have hra : a - (top (d + 1) a).choose (d + 2) < (top (d + 1) a).choose (d + 1) := by
        have h2 := lt_succ_top_choose (d + 1) a
        rw [e1, Nat.choose_succ_succ'] at h2
        simp only [e1] at h2
        omega
      have hK : d + 1 ≤ top (d + 1) a := by
        by_contra hK
        rw [Nat.choose_eq_zero_of_lt (show top (d + 1) a < d + 1 by omega)] at hra
        omega
      have hrem : macaulayPow (d + 1) (a - (top (d + 1) a).choose (d + 2)) <
          (top (d + 1) a + 1).choose (d + 2) := by
        have := ih _ _ hra
        rwa [macaulayPow_succ_choose d (top (d + 1) a) (by omega)] at this
      have hpascal : (top (d + 1) a + 1 + 1).choose (d + 2 + 1) =
          (top (d + 1) a + 1).choose (d + 2) + (top (d + 1) a + 1).choose (d + 2 + 1) :=
        Nat.choose_succ_succ' _ _
      have e3 : d + 2 + 1 = d + 3 := rfl
      simp only [e3] at hpascal
      have hle : (top (d + 1) a + 1 + 1).choose (d + 3) ≤ (top (d + 1) b + 1).choose (d + 3) :=
        Nat.choose_le_choose _ (by omega)
      omega
    ·
      have hr : a - (top (d + 1) a).choose (d + 2) < b - (top (d + 1) b).choose (d + 2) := by
        rw [← heq]; omega
      have := ih _ _ hr
      rw [heq] at this ⊢
      omega

private lemma  macaulayPow_strictMono {d : ℕ} (hd : 1 ≤ d) {a b : ℕ} (h : a < b) :
  macaulayPow d a < macaulayPow d b := by
  obtain ⟨d, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  exact strictMono_succ d a b h
@[path]
private lemma main
  {d : ℕ}
  {a b : ℕ}
-- given
  (hd : 1 ≤ d)
  (h : a < b) :
-- imply
  Nat.macaulayPow d a < Nat.macaulayPow d b :=
-- proof
  macaulayPow_strictMono hd h


-- created on 2026-10-23
