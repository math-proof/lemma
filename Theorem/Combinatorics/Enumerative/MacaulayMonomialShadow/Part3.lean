/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Fin.Tuple
import Def.Combinatorics.Enumerative.MacaulayMonomialShadow.Part2


namespace MetaMathlibExt

open BigOperators

section

/-- Any strict cascade representing `n` computes the canonical Macaulay value. -/
lemma mms_macaulay_eq (r n : ℕ) (digits : Fin r → ℕ) (hr : 0 < r)
    (hstrict : StrictMono digits)
    (hsum : n = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
    mms_macaulay r n =
      ∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1 := by
  have hdigits : digits = mms_digits r n :=
    mms_rep_unique r digits (mms_digits r n) hstrict (mms_digits_strict r n hr)
      (hsum.symm.trans (mms_digits_sum r n hr))
  rw [hdigits]
  rfl

/-- Split the top term from a Macaulay cascade. -/
lemma mms_macaulay_split (r n : ℕ) (digits : Fin (r + 1) → ℕ)
    (hstrict : StrictMono digits)
    (hsum : n = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
    mms_macaulay (r + 1) n =
      (if digits (Fin.last r) = 0 then 0
       else Nat.choose (digits (Fin.last r) - 1) r) +
        mms_macaulay r (n - Nat.choose (digits (Fin.last r)) (r + 1)) := by
  let lower : Fin r → ℕ := fun i => digits i.castSucc
  have hlower : StrictMono lower := hstrict.comp Fin.strictMono_castSucc
  have hcard : n = (∑ i, Nat.choose (lower i) (i.1 + 1)) +
      Nat.choose (digits (Fin.last r)) (r + 1) := by
    rw [Fin.sum_univ_castSucc] at hsum
    simpa only [lower, Fin.val_castSucc, Fin.val_last] using hsum
  have hrem : n - Nat.choose (digits (Fin.last r)) (r + 1) =
      ∑ i, Nat.choose (lower i) (i.1 + 1) := by omega
  rw [mms_macaulay_eq (r + 1) n digits (by omega) hstrict hsum,
    Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  by_cases hr : r = 0
  · subst r
    simp [mms_macaulay]
  · rw [mms_macaulay_eq r (n - Nat.choose (digits (Fin.last r)) (r + 1)) lower
      (Nat.pos_of_ne_zero hr) hlower hrem]
    dsimp [lower]
    rw [add_comm]

/-- Macaulay value immediately before a complete binomial block. -/
lemma mms_macaulay_choose_sub_one (r c : ℕ) (hr : 0 < r) (hrc : r ≤ c) :
    mms_macaulay r (Nat.choose c r - 1) =
      if c = r then 0 else Nat.choose (c - 1) (r - 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  let digits : Fin (s + 1) → ℕ := fun i => c - (s + 1) + i.1
  have hstrict : StrictMono digits := by
    intro i j hij
    dsimp [digits]
    omega
  have hsum : Nat.choose c (s + 1) - 1 =
      ∑ i, Nat.choose (digits i) (i.1 + 1) := by
    rw [mms_hockey_succ (c - (s + 1)) (s + 1)]
    congr 2
    omega
  rw [mms_macaulay_eq (s + 1) (Nat.choose c (s + 1) - 1) digits (by omega)
    hstrict hsum]
  by_cases hc : c = s + 1
  · subst c
    simp only [Nat.succ_eq_add_one, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hi0 : i.1 = 0
    · simp [digits, hi0]
    · simp only [digits, Nat.sub_self, zero_add, hi0, ↓reduceIte]
      exact Nat.choose_eq_zero_of_lt (by omega)
  · simp only [hc, ↓reduceIte]
    have hbase : 0 < c - (s + 1) := by omega
    simp only [digits, show ∀ i : Fin (s + 1), c - (s + 1) + i.1 ≠ 0 by
      intro i
      omega, ↓reduceIte]
    rw [show s + 1 - 1 = s by omega]
    calc
      (∑ i : Fin (s + 1), Nat.choose (c - (s + 1) + i.1 - 1) i.1) =
          ∑ i : Fin (s + 1), Nat.choose (c - (s + 1) - 1 + i.1) i.1 := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        omega
      _ = Nat.choose (c - (s + 1) - 1 + s + 1) s :=
        mms_hockey (c - (s + 1) - 1) s
      _ = Nat.choose (c - 1) s := by
        congr 1
        omega

/-- The Macaulay value of zero is zero at every rank. -/
lemma mms_macaulay_zero (r : ℕ) : mms_macaulay r 0 = 0 := by
  obtain rfl | hr := Nat.eq_zero_or_pos r
  · simp [mms_macaulay]
  · simpa using mms_macaulay_choose_sub_one r r hr le_rfl

/-- The top digit of the canonical cascade is monotone in the represented number. -/
lemma mms_digits_last_mono (r n m : ℕ) (hnm : n ≤ m) :
    mms_digits (r + 1) n (Fin.last r) ≤ mms_digits (r + 1) m (Fin.last r) := by
  let dn := mms_digits (r + 1) n
  let dm := mms_digits (r + 1) m
  have hdn : StrictMono dn := mms_digits_strict (r + 1) n (by omega)
  have hdm : StrictMono dm := mms_digits_strict (r + 1) m (by omega)
  have hnsum := mms_digits_sum (r + 1) n (by omega)
  have hmsum := mms_digits_sum (r + 1) m (by omega)
  by_contra! h
  change dm (Fin.last r) < dn (Fin.last r) at h
  change n = ∑ i, Nat.choose (dn i) (i.1 + 1) at hnsum
  change m = ∑ i, Nat.choose (dm i) (i.1 + 1) at hmsum
  have hnTop : Nat.choose (dn (Fin.last r)) (r + 1) ≤ n := by
    rw [hnsum, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    exact Nat.le_add_left _ _
  have hmBound : m < Nat.choose (dm (Fin.last r) + 1) (r + 1) := by
    rw [hmsum]
    apply mms_rep_sum_lt (r + 1) (dm (Fin.last r) + 1) dm hdm
    intro i
    have := hdm.monotone (Fin.le_last i)
    omega
  have hchoose : Nat.choose (dm (Fin.last r) + 1) (r + 1) ≤
      Nat.choose (dn (Fin.last r)) (r + 1) :=
    Nat.choose_le_choose (r + 1) (by omega)
  omega

/-- Increasing the input by one increases its Macaulay value by at most one. -/
lemma mms_macaulay_succ_le (r n : ℕ) :
    mms_macaulay r (n + 1) ≤ mms_macaulay r n + 1 := by
  induction r generalizing n with
  | zero => simp [mms_macaulay]
  | succ r ih =>
    let dn := mms_digits (r + 1) n
    let ds := mms_digits (r + 1) (n + 1)
    have hdn : StrictMono dn := mms_digits_strict (r + 1) n (by omega)
    have hds : StrictMono ds := mms_digits_strict (r + 1) (n + 1) (by omega)
    have hnsum := mms_digits_sum (r + 1) n (by omega)
    have hssum := mms_digits_sum (r + 1) (n + 1) (by omega)
    change n = ∑ i, Nat.choose (dn i) (i.1 + 1) at hnsum
    change n + 1 = ∑ i, Nat.choose (ds i) (i.1 + 1) at hssum
    have htopLe : dn (Fin.last r) ≤ ds (Fin.last r) :=
      mms_digits_last_mono r n (n + 1) (by omega)
    have hnBound : n < Nat.choose (dn (Fin.last r) + 1) (r + 1) := by
      rw [hnsum]
      apply mms_rep_sum_lt (r + 1) (dn (Fin.last r) + 1) dn hdn
      intro i
      have := hdn.monotone (Fin.le_last i)
      omega
    have hsTop : Nat.choose (ds (Fin.last r)) (r + 1) ≤ n + 1 := by
      rw [hssum, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_left _ _
    have htopSucc : ds (Fin.last r) ≤ dn (Fin.last r) + 1 := by
      by_contra! h
      have hrle : r + 1 ≤ dn (Fin.last r) + 1 := by
        by_contra! hsmall
        have hz := Nat.choose_eq_zero_of_lt hsmall
        omega
      have hlt := mms_choose_lt_succ (r + 1) (dn (Fin.last r) + 1)
        (by omega) (by omega)
      change Nat.choose (dn (Fin.last r) + 1) (r + 1) <
        Nat.choose (dn (Fin.last r) + 2) (r + 1) at hlt
      have hmono : Nat.choose (dn (Fin.last r) + 2) (r + 1) ≤
          Nat.choose (ds (Fin.last r)) (r + 1) :=
        Nat.choose_le_choose (r + 1) (by omega)
      omega
    have hcases : ds (Fin.last r) = dn (Fin.last r) ∨
        ds (Fin.last r) = dn (Fin.last r) + 1 := by omega
    rcases hcases with hsame | hcarry
    · have hsplitn := mms_macaulay_split r n dn hdn hnsum
      have hsplits := mms_macaulay_split r (n + 1) ds hds hssum
      have htopCard : Nat.choose (dn (Fin.last r)) (r + 1) ≤ n := by
        rw [hnsum, Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        exact Nat.le_add_left _ _
      have hrem : n + 1 - Nat.choose (ds (Fin.last r)) (r + 1) =
          (n - Nat.choose (dn (Fin.last r)) (r + 1)) + 1 := by
        rw [hsame]
        omega
      have hrec := ih (n - Nat.choose (dn (Fin.last r)) (r + 1))
      rw [hsame] at hsplits hrem
      rw [hsplits, hsplitn, hrem]
      exact Nat.add_le_add_left hrec _
    · have hnEq : n + 1 = Nat.choose (ds (Fin.last r)) (r + 1) := by
        have hnle : n + 1 ≤ Nat.choose (dn (Fin.last r) + 1) (r + 1) := by omega
        rw [← hcarry] at hnle
        omega
      have hsplits := mms_macaulay_split r (n + 1) ds hds hssum
      have hsVal : mms_macaulay (r + 1) (n + 1) =
          Nat.choose (dn (Fin.last r)) r := by
        rw [hsplits, hnEq, Nat.sub_self, mms_macaulay_zero, add_zero, hcarry]
        simp only [show dn (Fin.last r) + 1 ≠ 0 by omega, ↓reduceIte,
          Nat.add_sub_cancel]
      have hold := mms_macaulay_choose_sub_one (r + 1) (ds (Fin.last r))
        (by omega) (by
          have hrle : r ≤ dn (Fin.last r) := by
            by_contra! hsmall
            have hz := Nat.choose_eq_zero_of_lt
              (show dn (Fin.last r) + 1 < r + 1 by omega)
            omega
          omega)
      have hnPred : Nat.choose (ds (Fin.last r)) (r + 1) - 1 = n := by omega
      rw [hnPred] at hold
      rw [hsVal, hold, hcarry]
      by_cases hc : dn (Fin.last r) = r
      · simp [hc]
      · simp only [show dn (Fin.last r) + 1 ≠ r + 1 by omega, ↓reduceIte]
        rw [show dn (Fin.last r) + 1 - 1 = dn (Fin.last r) by omega,
          show r + 1 - 1 = r by omega]
        exact Nat.le_add_right _ _

/-- Every shifted cascade computes the canonical Macaulay value. -/
lemma mms_macaulay_extended (r n : ℕ) (hr : 0 < r) (ext : Fin (r + 1) → ℕ)
    (hext : StrictMono ext)
    (hsum : n = ∑ i, Nat.choose (ext i) i.1) :
    mms_macaulay r n =
      ∑ i, if i.1 = 0 then 0 else Nat.choose (ext i - 1) (i.1 - 1) := by
  induction r using Nat.strong_induction_on generalizing n with
  | h r ih =>
    obtain rfl | s := r
    · omega
    obtain rfl | s := s
    · let std : Fin 1 → ℕ := fun _ => n
      have hstd : StrictMono std := by
        intro i j hij
        omega
      have hstdsum : n = ∑ i, Nat.choose (std i) (i.1 + 1) := by simp [std]
      have hn : n = 1 + ext ⟨1, by omega⟩ := by
        simpa [Fin.sum_univ_succ] using hsum
      have hnpos : n ≠ 0 := by omega
      rw [mms_macaulay_eq 1 n std (by omega) hstd hstdsum]
      simp [std, hnpos]
    · let d := mms_digits (s + 2) n
      have hd : StrictMono d := mms_digits_strict (s + 2) n (by omega)
      have hdsum := mms_digits_sum (s + 2) n (by omega)
      change n = ∑ i, Nat.choose (d i) (i.1 + 1) at hdsum
      let q := d (Fin.last (s + 1))
      let e := ext (Fin.last (s + 2))
      have hStdBound : n < Nat.choose (q + 1) (s + 2) := by
        rw [hdsum]
        apply mms_rep_sum_lt (s + 2) (q + 1) d hd
        intro i
        have hi := hd.monotone (Fin.le_last i)
        change d i < d (Fin.last (s + 1)) + 1
        omega
      have hExtTop : Nat.choose e (s + 2) ≤ n := by
        rw [hsum, Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        exact Nat.le_add_left _ _
      have heq : e ≤ q := by
        by_contra! h
        have hchoose : Nat.choose (q + 1) (s + 2) ≤ Nat.choose e (s + 2) :=
          Nat.choose_le_choose (s + 2) (by omega)
        omega
      rcases heq.eq_or_lt with heq | heq
      · have hsplit := mms_macaulay_split (s + 1) n d hd hdsum
        let extLower : Fin (s + 2) → ℕ := fun i => ext i.castSucc
        have hextLower : StrictMono extLower := hext.comp Fin.strictMono_castSucc
        let nLower := ∑ i, Nat.choose (extLower i) i.1
        have hrec := ih (s + 1) (by omega) nLower (by omega) extLower hextLower rfl
        have hrem : n - Nat.choose q (s + 2) = nLower := by
          have hcard : (∑ i : Fin (s + 1), Nat.choose (d i.castSucc) (i.1 + 1)) =
              nLower := by
            have hdSplit := hdsum
            rw [Fin.sum_univ_castSucc] at hdSplit
            simp only [Fin.val_castSucc, Fin.val_last] at hdSplit
            have heSplit := hsum
            rw [Fin.sum_univ_castSucc] at heSplit
            simp only [Fin.val_castSucc, Fin.val_last] at heSplit
            change n = nLower + Nat.choose e (s + 2) at heSplit
            change n = (∑ i : Fin (s + 1), Nat.choose (d i.castSucc) (i.1 + 1)) +
              Nat.choose q (s + 2) at hdSplit
            rw [heq] at heSplit
            omega
          have hdSplit := hdsum
          rw [Fin.sum_univ_castSucc] at hdSplit
          simp only [Fin.val_castSucc, Fin.val_last] at hdSplit
          change n = (∑ i : Fin (s + 1), Nat.choose (d i.castSucc) (i.1 + 1)) +
            Nat.choose q (s + 2) at hdSplit
          omega
        rw [hsplit, hrem]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [show ext (Fin.last (s + 2)) = e by rfl, heq]
        dsimp [extLower] at hrec
        rw [hrec]
        have hq : q ≠ 0 := by
          have hv := mms_digits_val_le (s + 1) d hd (Fin.last (s + 1))
          change s + 1 ≤ q at hv
          omega
        change (if q = 0 then 0 else Nat.choose (q - 1) (s + 1)) +
          (∑ i : Fin (s + 2), if i.1 = 0 then 0 else
            Nat.choose (ext i.castSucc - 1) (i.1 - 1)) =
          (∑ i : Fin (s + 2), if i.1 = 0 then 0 else
            Nat.choose (ext i.castSucc - 1) (i.1 - 1)) +
          Nat.choose (q - 1) (s + 1)
        simp only [hq, ↓reduceIte]
        rw [add_comm]
      · have hExtBound : n ≤ Nat.choose (e + 1) (s + 2) := by
          rw [hsum]
          exact mms_shifted_sum_le (s + 2) ext hext
        have hStdTop : Nat.choose q (s + 2) ≤ n := by
          rw [hdsum, Fin.sum_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last]
          exact Nat.le_add_left _ _
        have hchoose : Nat.choose (e + 1) (s + 2) ≤ Nat.choose q (s + 2) :=
          Nat.choose_le_choose (s + 2) (by omega)
        have hnEq : n = Nat.choose q (s + 2) := by omega
        have hchooseEq : Nat.choose (e + 1) (s + 2) = Nat.choose q (s + 2) := by omega
        have hq : q = e + 1 := by
          by_contra! hne
          have heVal : s + 2 ≤ e := by
            have hv := mms_digits_val_le (s + 2) ext hext (Fin.last (s + 2))
            simpa only [Fin.val_last] using hv
          have hlt := mms_choose_lt_succ (s + 2) (e + 1) (by omega) (by omega)
          rw [show e + 1 + 1 = e + 2 by omega] at hlt
          have hmono : Nat.choose (e + 2) (s + 2) ≤ Nat.choose q (s + 2) :=
            Nat.choose_le_choose (s + 2) (by omega)
          omega
        have hExtLower := mms_shifted_lower_max (s + 1) ext hext (by
          rw [← hsum, hnEq, hq])
        change (∑ i, if i.1 = 0 then 0 else Nat.choose (ext i - 1) (i.1 - 1)) =
          Nat.choose e (s + 1) at hExtLower
        have hsplit := mms_macaulay_split (s + 1) n d hd hdsum
        rw [hsplit, hnEq, Nat.sub_self, mms_macaulay_zero, add_zero]
        rw [hExtLower]
        change (if q = 0 then 0 else Nat.choose (q - 1) (s + 1)) =
          Nat.choose e (s + 1)
        rw [hq]
        simp

/-- Adding a bounded remainder below a leading binomial splits the Macaulay value. -/
lemma mms_macaulay_choose_add (r q x : ℕ) (hrq : r + 1 ≤ q)
    (hx : x < Nat.choose q r) :
    mms_macaulay (r + 1) (Nat.choose q (r + 1) + x) =
      Nat.choose (q - 1) r + mms_macaulay r x := by
  obtain ⟨lower, hlower, hlowerq, hlowerSum⟩ := mms_exists_rep_lt r q x hx
  let digits : Fin (r + 1) → ℕ := Fin.snoc lower q
  have hstrict : StrictMono digits := mms_strictMono_snoc hlower hlowerq
  have hsum : Nat.choose q (r + 1) + x =
      ∑ i, Nat.choose (digits i) (i.1 + 1) := by
    rw [Fin.sum_univ_castSucc]
    simp only [digits, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    rw [← hlowerSum]
    omega
  rw [mms_macaulay_eq (r + 1) (Nat.choose q (r + 1) + x) digits (by omega) hstrict hsum,
    Fin.sum_univ_castSucc]
  simp only [digits, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have hq : q ≠ 0 := by omega
  simp only [hq, ↓reduceIte]
  have hlowerMac :
      (∑ i : Fin r, if lower i = 0 then 0 else
        Nat.choose (lower i - 1) i.1) = mms_macaulay r x := by
    by_cases hr0 : r = 0
    · subst r
      simp [mms_macaulay]
    · rw [mms_macaulay_eq r x lower (by omega) hlower hlowerSum]
  rw [hlowerMac]
  rw [add_comm]

/-- A positive cascade either has a shifted representation or gains one under Macaulay. -/
lemma mms_extended_or_step (r a : ℕ) (hr : 0 < r) (ha : 0 < a) :
    (∃ ext : Fin (r + 1) → ℕ, StrictMono ext ∧
      a = ∑ i, Nat.choose (ext i) i.1) ∨
      mms_macaulay r a = mms_macaulay r (a - 1) + 1 := by
  induction r using Nat.strong_induction_on generalizing a with
  | h r ih =>
    obtain rfl | s := r
    · omega
    let d := mms_digits (s + 1) a
    have hd : StrictMono d := mms_digits_strict (s + 1) a (by omega)
    have hdsum := mms_digits_sum (s + 1) a (by omega)
    change a = ∑ i, Nat.choose (d i) (i.1 + 1) at hdsum
    let q := d (Fin.last s)
    let x := a - Nat.choose q (s + 1)
    have hq : s + 1 ≤ q := by
      have hv := mms_digits_val_le s d hd (Fin.last s)
      change s ≤ q at hv
      by_contra! hnot
      have hbound : a < Nat.choose (q + 1) (s + 1) := by
        rw [hdsum]
        apply mms_rep_sum_lt (s + 1) (q + 1) d hd
        intro i
        have hi := hd.monotone (Fin.le_last i)
        change d i < d (Fin.last s) + 1
        omega
      have hqr : q = s := by omega
      rw [hqr] at hbound
      simp at hbound
      omega
    have htop : Nat.choose q (s + 1) ≤ a := by
      rw [hdsum, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_left _ _
    have haSplit : a = Nat.choose q (s + 1) + x := by omega
    have hx : x < Nat.choose q s := by
      have hsplit := hdsum
      rw [Fin.sum_univ_castSucc] at hsplit
      simp only [Fin.val_castSucc, Fin.val_last] at hsplit
      change a = (∑ i : Fin s, Nat.choose (d i.castSucc) (i.1 + 1)) +
        Nat.choose q (s + 1) at hsplit
      have hlt := mms_rep_sum_lt s q (fun i => d i.castSucc)
        (hd.comp Fin.strictMono_castSucc) (fun i => hd (Fin.castSucc_lt_last i))
      omega
    by_cases hx0 : x = 0
    · by_cases hqr : q = s + 1
      · right
        rw [haSplit, hx0, add_zero, hqr]
        have hcur := mms_macaulay_choose_add s (s + 1) 0 le_rfl (by simp)
        simpa only [Nat.choose_self, add_zero, Nat.sub_self, Nat.add_sub_cancel,
          mms_macaulay_zero, zero_add] using hcur
      · left
        let ext : Fin (s + 2) → ℕ := fun i => q - (s + 1) - 1 + i.1
        have hext : StrictMono ext := by
          intro i j hij
          dsimp [ext]
          omega
        refine ⟨ext, hext, ?_⟩
        rw [mms_hockey (q - (s + 1) - 1) (s + 1)]
        rw [haSplit, hx0, add_zero]
        congr 2
        omega
    · have hs : 0 < s := by
        by_contra! hnot
        have : s = 0 := by omega
        subst s
        simp at hx
        omega
      rcases ih s (by omega) x hs (by omega) with hext | hstep
      · obtain ⟨lower, hlower, hlowerSum⟩ := hext
        have hlast : lower (Fin.last s) < q := by
          by_contra! hnot
          have hchoose : Nat.choose q s ≤ Nat.choose (lower (Fin.last s)) s :=
            Nat.choose_le_choose s (by omega)
          have hterm : Nat.choose (lower (Fin.last s)) s ≤ x := by
            have hLowerSplit := hlowerSum
            rw [Fin.sum_univ_castSucc] at hLowerSplit
            simp only [Fin.val_castSucc, Fin.val_last] at hLowerSplit
            omega
          omega
        have hlowerTop : ∀ i, lower i < q := by
          intro i
          exact (hlower.monotone (Fin.le_last i)).trans_lt hlast
        left
        refine ⟨Fin.snoc lower q, mms_strictMono_snoc hlower hlowerTop, ?_⟩
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [← hlowerSum, haSplit, add_comm]
      · right
        rw [haSplit]
        have hcur := mms_macaulay_choose_add s q x hq hx
        have hpred : Nat.choose q (s + 1) + x - 1 =
            Nat.choose q (s + 1) + (x - 1) := by omega
        have hprev := mms_macaulay_choose_add s q (x - 1) hq (by omega)
        rw [hpred, hcur, hprev, hstep]
        omega

/-- A Macaulay value is at most its input. -/
lemma mms_macaulay_le_self (r n : ℕ) : mms_macaulay r n ≤ n := by
  induction n with
  | zero => rw [mms_macaulay_zero]
  | succ n ih =>
    have hstep := mms_macaulay_succ_le r n
    omega

/-- Under the split hypothesis, the three leading cascade digits interlace. -/
lemma mms_top_comparison (k n a b : ℕ) (hadd : a + b = n)
    (hlt : a < mms_macaulay (k + 2) n)
    (da : Fin (k + 1) → ℕ) (dn db : Fin (k + 2) → ℕ)
    (_hda : StrictMono da) (hdn : StrictMono dn) (hdb : StrictMono db)
    (hasum : a = ∑ i, Nat.choose (da i) (i.1 + 1))
    (hnsum : n = ∑ i, Nat.choose (dn i) (i.1 + 1))
    (hbsum : b = ∑ i, Nat.choose (db i) (i.1 + 1)) :
    da (Fin.last k) < dn (Fin.last (k + 1)) ∧
      dn (Fin.last (k + 1)) ≤ db (Fin.last (k + 1)) + 1 := by
  let A := da (Fin.last k)
  let N := dn (Fin.last (k + 1))
  let B := db (Fin.last (k + 1))
  have hma := mms_macaulay_eq (k + 2) n dn (by omega) hdn hnsum
  constructor
  · by_contra! hnot
    have hbound :
        (∑ i, if dn i = 0 then 0 else Nat.choose (dn i - 1) i.1) ≤
          Nat.choose N (k + 1) := by
      apply mms_lower_sum_le (k + 1) (N + 1) dn hdn
      intro i
      have hi := hdn.monotone (Fin.le_last i)
      change dn i < dn (Fin.last (k + 1)) + 1
      omega
    have hchooseNA : Nat.choose N (k + 1) ≤ Nat.choose A (k + 1) :=
      Nat.choose_le_choose (k + 1) (by omega)
    have htopA : Nat.choose A (k + 1) ≤ a := by
      rw [hasum, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_left _ _
    rw [hma] at hlt
    omega
  · by_contra! hnot
    have hbBound : b < Nat.choose (B + 1) (k + 2) := by
      rw [hbsum]
      apply mms_rep_sum_lt (k + 2) (B + 1) db hdb
      intro i
      have hi := hdb.monotone (Fin.le_last i)
      change db i < db (Fin.last (k + 1)) + 1
      omega
    have hBN : B + 1 ≤ N - 1 := by omega
    have hbN : b < Nat.choose (N - 1) (k + 2) :=
      lt_of_lt_of_le hbBound (Nat.choose_le_choose (k + 2) hBN)
    have htopN : Nat.choose N (k + 2) ≤ n := by
      rw [hnsum, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_left _ _
    let rem := n - Nat.choose N (k + 2)
    have hnSplit : n = Nat.choose N (k + 2) + rem := by omega
    have hsplit := mms_macaulay_split (k + 1) n dn hdn hnsum
    have hNpos : N ≠ 0 := by
      have hv := mms_digits_val_le (k + 1) dn hdn (Fin.last (k + 1))
      change k + 1 ≤ N at hv
      omega
    rw [show dn (Fin.last (k + 1)) = N by rfl,
      show n - Nat.choose N (k + 2) = rem by rfl] at hsplit
    simp only [hNpos, ↓reduceIte] at hsplit
    change mms_macaulay (k + 2) n = Nat.choose (N - 1) (k + 1) +
      mms_macaulay (k + 1) rem at hsplit
    have hrem := mms_macaulay_le_self (k + 1) rem
    have hpascal : Nat.choose N (k + 2) =
        Nat.choose (N - 1) (k + 1) + Nat.choose (N - 1) (k + 2) := by
      have hp := Nat.choose_succ_succ (N - 1) (k + 1)
      have hpred : (N - 1).succ = N := by omega
      rw [hpred] at hp
      simpa only [Nat.succ_eq_add_one] using hp
    have hmBound : mms_macaulay (k + 2) n ≤ n - Nat.choose (N - 1) (k + 2) := by
      rw [hsplit, hnSplit, hpascal]
      omega
    omega

/-- Min/max redistribution lowers the first summand and preserves the two Macaulay values. -/
lemma mms_redistribute (r a b : ℕ)
    (da : Fin (r + 1) → ℕ) (db ext : Fin (r + 2) → ℕ)
    (hda : StrictMono da) (hdb : StrictMono db) (hext : StrictMono ext)
    (hasum : a = ∑ i, Nat.choose (da i) (i.1 + 1))
    (hbsum : b = ∑ i, Nat.choose (db i) (i.1 + 1))
    (haext : a = ∑ i, Nat.choose (ext i) i.1)
    (htop : da (Fin.last r) < db (Fin.last (r + 1))) :
    ∃ alpha beta : ℕ, alpha < a ∧ alpha + beta = a + b ∧
      mms_macaulay (r + 1) alpha + mms_macaulay (r + 2) beta =
        mms_macaulay (r + 1) a + mms_macaulay (r + 2) b := by
  let left : Fin (r + 1) → ℕ := fun i => min (ext i.succ) (db i.castSucc)
  let right : Fin (r + 1) → ℕ := fun i => max (ext i.succ) (db i.castSucc)
  let tail : Fin (r + 2) → ℕ := Fin.snoc right (db (Fin.last (r + 1)))
  let betaDigits : Fin (r + 3) → ℕ := Fin.cons (ext 0) tail
  let alpha := ∑ i, Nat.choose (left i) (i.1 + 1)
  let beta := ∑ i, Nat.choose (betaDigits i) i.1
  have hleft : StrictMono left := by
    intro i j hij
    apply min_lt_min
    · exact hext (Fin.strictMono_succ hij)
    · exact hdb (Fin.strictMono_castSucc hij)
  have hright : StrictMono right := by
    intro i j hij
    apply max_lt_max
    · exact hext (Fin.strictMono_succ hij)
    · exact hdb (Fin.strictMono_castSucc hij)
  have hextTopLe : ext (Fin.last (r + 1)) ≤ da (Fin.last r) := by
    by_contra! hnot
    have haBound : a < Nat.choose (da (Fin.last r) + 1) (r + 1) := by
      rw [hasum]
      apply mms_rep_sum_lt (r + 1) (da (Fin.last r) + 1) da hda
      intro i
      have hi := hda.monotone (Fin.le_last i)
      omega
    have htopTerm : Nat.choose (ext (Fin.last (r + 1))) (r + 1) ≤ a := by
      rw [haext, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_left _ _
    have hchoose : Nat.choose (da (Fin.last r) + 1) (r + 1) ≤
        Nat.choose (ext (Fin.last (r + 1))) (r + 1) :=
      Nat.choose_le_choose (r + 1) (by omega)
    omega
  have hextDb : ext (Fin.last (r + 1)) < db (Fin.last (r + 1)) :=
    hextTopLe.trans_lt htop
  have htail : StrictMono tail := by
    apply mms_strictMono_snoc hright
    intro i
    apply max_lt
    · exact (hext.monotone (Fin.le_last i.succ)).trans_lt hextDb
    · exact hdb (Fin.castSucc_lt_last i)
  have hbetaDigits : StrictMono betaDigits := by
    rw [Fin.strictMono_cons]
    refine ⟨?_, htail⟩
    intro j
    rcases j.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
    · simp only [tail, Fin.snoc_castSucc, right]
      exact (hext (Fin.mk_lt_mk.mpr (by simp))).trans_le (le_max_left _ _)
    · simp only [tail, Fin.snoc_last]
      exact (hext.monotone (Fin.le_last (0 : Fin (r + 2)))).trans_lt hextDb
  have hpair (i : Fin (r + 1)) :
      Nat.choose (left i) (i.1 + 1) + Nat.choose (right i) (i.1 + 1) =
        Nat.choose (ext i.succ) (i.1 + 1) + Nat.choose (db i.castSucc) (i.1 + 1) := by
    dsimp [left, right]
    rcases le_total (ext i.succ) (db i.castSucc) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      omega
  have hpairSum :
      (∑ i : Fin (r + 1), Nat.choose (left i) (i.1 + 1)) +
          ∑ i : Fin (r + 1), Nat.choose (right i) (i.1 + 1) =
        (∑ i : Fin (r + 1), Nat.choose (ext i.succ) (i.1 + 1)) +
          ∑ i : Fin (r + 1), Nat.choose (db i.castSucc) (i.1 + 1) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hpair i
  have haSplit : a = 1 + ∑ i : Fin (r + 1),
      Nat.choose (ext i.succ) (i.1 + 1) := by
    rw [haext, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.choose_zero_right, Fin.val_succ]
  have hbSplit : b = (∑ i : Fin (r + 1), Nat.choose (db i.castSucc) (i.1 + 1)) +
      Nat.choose (db (Fin.last (r + 1))) (r + 2) := by
    rw [hbsum, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
  have hbetaSplit : beta = 1 +
      (∑ i : Fin (r + 1), Nat.choose (right i) (i.1 + 1)) +
      Nat.choose (db (Fin.last (r + 1))) (r + 2) := by
    dsimp [beta]
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [betaDigits, Fin.cons_zero, Fin.cons_succ, tail, Fin.snoc_castSucc,
      Fin.snoc_last, Fin.val_zero, Nat.choose_zero_right, Fin.val_succ,
      Fin.val_castSucc, Fin.val_last]
    rw [show r + 1 + 1 = r + 2 by omega]
    rw [Nat.add_assoc]
  have halphaLe : alpha ≤ ∑ i : Fin (r + 1),
      Nat.choose (ext i.succ) (i.1 + 1) := by
    dsimp [alpha]
    apply Finset.sum_le_sum
    intro i _
    exact Nat.choose_le_choose (i.1 + 1) (min_le_left _ _)
  have halpha : alpha < a := by omega
  have hab : alpha + beta = a + b := by omega
  have hleftMac := mms_macaulay_eq (r + 1) alpha left (by omega) hleft rfl
  have hbetaMac := mms_macaulay_extended (r + 2) beta (by omega) betaDigits hbetaDigits rfl
  have haMac := mms_macaulay_extended (r + 1) a (by omega) ext hext haext
  have hbMac := mms_macaulay_eq (r + 2) b db (by omega) hdb hbsum
  have hextPos (i : Fin (r + 1)) : ext i.succ ≠ 0 := by
    have hi := hext (Fin.mk_lt_mk.mpr (by simp) : (0 : Fin (r + 2)) < i.succ)
    exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hi)
  have hdbTopPos : db (Fin.last (r + 1)) ≠ 0 := by
    have hv := mms_digits_val_le (r + 1) db hdb (Fin.last (r + 1))
    change r + 1 ≤ db (Fin.last (r + 1)) at hv
    omega
  have hshadowPair (i : Fin (r + 1)) :
      (if left i = 0 then 0 else Nat.choose (left i - 1) i.1) +
          Nat.choose (right i - 1) i.1 =
        Nat.choose (ext i.succ - 1) i.1 +
          (if db i.castSucc = 0 then 0 else Nat.choose (db i.castSucc - 1) i.1) := by
    dsimp [left, right]
    rcases le_total (ext i.succ) (db i.castSucc) with h | h
    · have hdbi : db i.castSucc ≠ 0 := by
        exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero (hextPos i)) h)
      simp [min_eq_left h, max_eq_right h, hextPos i, hdbi]
    · simp [min_eq_right h, max_eq_left h, add_comm]
  have hshadowPairSum :
      (∑ i : Fin (r + 1), if left i = 0 then 0 else
        Nat.choose (left i - 1) i.1) +
          ∑ i : Fin (r + 1), Nat.choose (right i - 1) i.1 =
        (∑ i : Fin (r + 1), Nat.choose (ext i.succ - 1) i.1) +
          ∑ i : Fin (r + 1), if db i.castSucc = 0 then 0 else
            Nat.choose (db i.castSucc - 1) i.1 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hshadowPair i
  have hbetaShadow :
      (∑ i, if i.1 = 0 then 0 else Nat.choose (betaDigits i - 1) (i.1 - 1)) =
        (∑ i : Fin (r + 1), Nat.choose (right i - 1) i.1) +
          Nat.choose (db (Fin.last (r + 1)) - 1) (r + 1) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_zero, ↓reduceIte, zero_add, Fin.val_succ, Nat.add_sub_cancel,
      betaDigits, Fin.cons_succ, tail, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_castSucc, Fin.val_last, show r + 2 ≠ 0 by omega,
      show ∀ i : Fin (r + 1), i.1 + 1 ≠ 0 by omega, ↓reduceIte]
  have haShadow :
      (∑ i, if i.1 = 0 then 0 else Nat.choose (ext i - 1) (i.1 - 1)) =
        ∑ i : Fin (r + 1), Nat.choose (ext i.succ - 1) i.1 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, ↓reduceIte, zero_add, Fin.val_succ, Nat.add_sub_cancel,
      show ∀ i : Fin (r + 1), i.1 + 1 ≠ 0 by omega, ↓reduceIte]
  have hbShadow :
      (∑ i, if db i = 0 then 0 else Nat.choose (db i - 1) i.1) =
        (∑ i : Fin (r + 1), if db i.castSucc = 0 then 0 else
          Nat.choose (db i.castSucc - 1) i.1) +
            Nat.choose (db (Fin.last (r + 1)) - 1) (r + 1) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, hdbTopPos, ↓reduceIte]
  refine ⟨alpha, beta, halpha, hab, ?_⟩
  rw [hleftMac, hbetaMac, haMac, hbMac, hbetaShadow, haShadow, hbShadow]
  omega

/-- The Ábrego--Fernández-Merchant--Llano split inequality for Macaulay values. -/
lemma mms_split_ineq (r n a b : ℕ) (hr : 0 < r) (hadd : a + b = n)
    (hlt : a < mms_macaulay (r + 1) n) :
    mms_macaulay r a + mms_macaulay (r + 1) b ≥ mms_macaulay (r + 1) n := by
  induction r using Nat.strong_induction_on generalizing n a b with
  | h r ihR =>
    obtain rfl | s := r
    · omega
    induction a using Nat.strong_induction_on generalizing n b with
    | h a ihA =>
      by_cases ha0 : a = 0
      · subst a
        have hb : b = n := by omega
        rw [hb, mms_macaulay_zero]
        omega
      have ha : 0 < a := Nat.pos_of_ne_zero ha0
      let da := mms_digits (s + 1) a
      let db := mms_digits (s + 2) b
      let dn := mms_digits (s + 2) n
      have hda : StrictMono da := mms_digits_strict (s + 1) a (by omega)
      have hdb : StrictMono db := mms_digits_strict (s + 2) b (by omega)
      have hdn : StrictMono dn := mms_digits_strict (s + 2) n (by omega)
      have hasum := mms_digits_sum (s + 1) a (by omega)
      have hbsum := mms_digits_sum (s + 2) b (by omega)
      have hnsum := mms_digits_sum (s + 2) n (by omega)
      change a = ∑ i, Nat.choose (da i) (i.1 + 1) at hasum
      change b = ∑ i, Nat.choose (db i) (i.1 + 1) at hbsum
      change n = ∑ i, Nat.choose (dn i) (i.1 + 1) at hnsum
      have hcomp := mms_top_comparison s n a b hadd hlt da dn db hda hdn hdb
        hasum hnsum hbsum
      by_cases hcase : da (Fin.last s) < db (Fin.last (s + 1))
      · rcases mms_extended_or_step (s + 1) a (by omega) ha with hext | hstep
        · obtain ⟨ext, hextMono, hextSum⟩ := hext
          obtain ⟨alpha, beta, halpha, hab, hmac⟩ :=
            mms_redistribute s a b da db ext hda hdb hextMono hasum hbsum hextSum hcase
          have halphaCond : alpha < mms_macaulay (s + 2) n := halpha.trans hlt
          have habn : alpha + beta = n := hab.trans hadd
          have hrec := ihA alpha halpha n beta habn halphaCond
          change mms_macaulay (s + 1) alpha + mms_macaulay (s + 2) beta ≥
            mms_macaulay (s + 2) n at hrec
          change mms_macaulay (s + 1) a + mms_macaulay (s + 2) b ≥
            mms_macaulay (s + 2) n
          omega
        · have hpred : a - 1 < a := by omega
          have hsum : a - 1 + (b + 1) = n := by omega
          have hcond : a - 1 < mms_macaulay (s + 2) n := hpred.trans hlt
          have hrec := ihA (a - 1) hpred n (b + 1) hsum hcond
          change mms_macaulay (s + 1) (a - 1) + mms_macaulay (s + 2) (b + 1) ≥
            mms_macaulay (s + 2) n at hrec
          have hsucc := mms_macaulay_succ_le (s + 2) b
          change mms_macaulay (s + 1) a + mms_macaulay (s + 2) b ≥
            mms_macaulay (s + 2) n
          omega
      · have htopA : da (Fin.last s) + 1 = dn (Fin.last (s + 1)) := by omega
        have htopB : db (Fin.last (s + 1)) + 1 = dn (Fin.last (s + 1)) := by omega
        let D := dn (Fin.last (s + 1))
        let a0 := a - Nat.choose (D - 1) (s + 1)
        let b0 := b - Nat.choose (D - 1) (s + 2)
        let n0 := n - Nat.choose D (s + 2)
        have hD : s + 2 ≤ D := by
          have hv := mms_digits_val_le s da hda (Fin.last s)
          change s ≤ da (Fin.last s) at hv
          have htopEq : da (Fin.last s) = D - 1 := by
            dsimp [D]
            omega
          by_contra! hnot
          have hdeq : da (Fin.last s) = s := by omega
          have hbound : a < Nat.choose (s + 1) (s + 1) := by
            rw [hasum]
            apply mms_rep_sum_lt (s + 1) (s + 1) da hda
            intro i
            have hi := hda.monotone (Fin.le_last i)
            rw [hdeq] at hi
            omega
          simp at hbound
          omega
        have htopAEq : da (Fin.last s) = D - 1 := by
          dsimp [D]
          omega
        have htopBEq : db (Fin.last (s + 1)) = D - 1 := by
          dsimp [D]
          omega
        have htopNEq : dn (Fin.last (s + 1)) = D := rfl
        have ha0sum : a0 = ∑ i : Fin s, Nat.choose (da i.castSucc) (i.1 + 1) := by
          have hs := hasum
          rw [Fin.sum_univ_castSucc] at hs
          simp only [Fin.val_castSucc, Fin.val_last] at hs
          rw [htopAEq] at hs
          dsimp [a0]
          omega
        have hb0sum : b0 = ∑ i : Fin (s + 1),
            Nat.choose (db i.castSucc) (i.1 + 1) := by
          have hs := hbsum
          rw [Fin.sum_univ_castSucc] at hs
          simp only [Fin.val_castSucc, Fin.val_last] at hs
          rw [htopBEq] at hs
          rw [show s + 1 + 1 = s + 2 by omega] at hs
          dsimp [b0]
          omega
        have hn0sum : n0 = ∑ i : Fin (s + 1),
            Nat.choose (dn i.castSucc) (i.1 + 1) := by
          have hs := hnsum
          rw [Fin.sum_univ_castSucc] at hs
          simp only [Fin.val_castSucc, Fin.val_last] at hs
          change n = (∑ i : Fin (s + 1), Nat.choose (dn i.castSucc) (i.1 + 1)) +
            Nat.choose D (s + 2) at hs
          dsimp [n0]
          omega
        have hpascalCard : Nat.choose D (s + 2) =
            Nat.choose (D - 1) (s + 1) + Nat.choose (D - 1) (s + 2) := by
          have hp := Nat.choose_succ_succ (D - 1) (s + 1)
          have hpred : (D - 1).succ = D := by omega
          rw [hpred] at hp
          simpa only [Nat.succ_eq_add_one] using hp
        have hab0 : a0 + b0 = n0 := by
          have haSplitCard : a = Nat.choose (D - 1) (s + 1) + a0 := by
            have hs := hasum
            rw [Fin.sum_univ_castSucc] at hs
            simp only [Fin.val_castSucc, Fin.val_last] at hs
            rw [htopAEq] at hs
            rw [← ha0sum] at hs
            omega
          have hbSplitCard : b = Nat.choose (D - 1) (s + 2) + b0 := by
            have hs := hbsum
            rw [Fin.sum_univ_castSucc] at hs
            simp only [Fin.val_castSucc, Fin.val_last] at hs
            rw [htopBEq, show s + 1 + 1 = s + 2 by omega] at hs
            rw [← hb0sum] at hs
            omega
          have hnSplitCard : n = Nat.choose D (s + 2) + n0 := by
            have hs := hnsum
            rw [Fin.sum_univ_castSucc] at hs
            simp only [Fin.val_castSucc, Fin.val_last] at hs
            change n = (∑ i : Fin (s + 1), Nat.choose (dn i.castSucc) (i.1 + 1)) +
              Nat.choose D (s + 2) at hs
            rw [← hn0sum] at hs
            omega
          omega
        have hnMac := mms_macaulay_split (s + 1) n dn hdn hnsum
        rw [htopNEq] at hnMac
        have hDne : D ≠ 0 := by omega
        simp only [hDne, ↓reduceIte] at hnMac
        change mms_macaulay (s + 2) n = Nat.choose (D - 1) (s + 1) +
          mms_macaulay (s + 1) n0 at hnMac
        have haSplit : a = Nat.choose (D - 1) (s + 1) + a0 := by
          have hs := hasum
          rw [Fin.sum_univ_castSucc] at hs
          simp only [Fin.val_castSucc, Fin.val_last] at hs
          rw [htopAEq] at hs
          dsimp [a0]
          omega
        have hcond0 : a0 < mms_macaulay (s + 1) n0 := by
          have ht := hlt
          rw [haSplit, hnMac] at ht
          omega
        have hrec : mms_macaulay s a0 + mms_macaulay (s + 1) b0 ≥
            mms_macaulay (s + 1) n0 := by
          by_cases hs0 : s = 0
          · subst s
            have ha00 : a0 = 0 := by simpa using ha0sum
            rw [ha00, mms_macaulay_zero]
            have hb0n0 : b0 = n0 := by omega
            rw [hb0n0]
            omega
          · exact ihR s (by omega) n0 a0 b0 (by omega) hab0 hcond0
        have haMac := mms_macaulay_split s a da hda hasum
        rw [htopAEq] at haMac
        have hDm1ne : D - 1 ≠ 0 := by omega
        simp only [hDm1ne, ↓reduceIte] at haMac
        change mms_macaulay (s + 1) a = Nat.choose (D - 1 - 1) s +
          mms_macaulay s a0 at haMac
        have hbMac := mms_macaulay_split (s + 1) b db hdb hbsum
        rw [htopBEq] at hbMac
        simp only [hDm1ne, ↓reduceIte] at hbMac
        change mms_macaulay (s + 2) b = Nat.choose (D - 1 - 1) (s + 1) +
          mms_macaulay (s + 1) b0 at hbMac
        have hpascalShadow : Nat.choose (D - 1) (s + 1) =
            Nat.choose (D - 1 - 1) s + Nat.choose (D - 1 - 1) (s + 1) := by
          have hp := Nat.choose_succ_succ (D - 1 - 1) s
          have hpred : (D - 1 - 1).succ = D - 1 := by omega
          rw [hpred] at hp
          simpa only [Nat.succ_eq_add_one] using hp
        rw [haMac, hbMac, hnMac, hpascalShadow]
        omega

end
end MetaMathlibExt
