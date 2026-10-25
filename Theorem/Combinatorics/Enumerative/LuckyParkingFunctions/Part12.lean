/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part11


section

namespace MetaMathlibExt

lemma embedMarked_unmarked (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
    (hfix : b.1 ⟨i0.val + 1, by omega⟩ = ⟨i0.val + 1, by omega⟩)
    (hmin : ∀ k : Fin (n + 1), 0 < k.val → k.val < i0.val + 1 → b.1 k ≠ k) :
    embedMarked n ⟨⟨unmarkedFun n b i0, unmarkedFun_mono n b i0 hfix,
      fun j => unmarkedFun_bound n b i0 hmin j⟩,
      ⟨i0, unmarkedFun_fixed n b i0 hfix⟩⟩ = b := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  by_cases h0 : k.val = 0
  · have hL : ((embedMarked n ⟨⟨unmarkedFun n b i0,
          unmarkedFun_mono n b i0 hfix,
          fun j => unmarkedFun_bound n b i0 hmin j⟩,
        ⟨i0, unmarkedFun_fixed n b i0 hfix⟩⟩).1 k).val = 0 :=
      markedFun_val_of_zero n _ i0 k h0
    have hb := b.2.2 k
    omega
  · by_cases h1 : k.val - 1 < i0.val
    · have hL : ((embedMarked n ⟨⟨unmarkedFun n b i0,
            unmarkedFun_mono n b i0 hfix,
            fun j => unmarkedFun_bound n b i0 hmin j⟩,
          ⟨i0, unmarkedFun_fixed n b i0 hfix⟩⟩).1 k).val =
          (unmarkedFun n b i0 ⟨k.val - 1, by omega⟩).val :=
        markedFun_val_of_lt n _ i0 k h0 h1
      have hlt : (⟨k.val - 1, by omega⟩ : Fin n).val < i0.val := h1
      have hU : (unmarkedFun n b i0 ⟨k.val - 1, by omega⟩).val =
          (b.1 ⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩).val :=
        unmarkedFun_val_of_lt n b i0 ⟨k.val - 1, by omega⟩ hlt
      have heq : (⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩ :
          Fin (n + 1)) = k := by
        apply Fin.ext
        simp only
        omega
      rw [hL, hU, heq]
    · have hL : ((embedMarked n ⟨⟨unmarkedFun n b i0,
            unmarkedFun_mono n b i0 hfix,
            fun j => unmarkedFun_bound n b i0 hmin j⟩,
          ⟨i0, unmarkedFun_fixed n b i0 hfix⟩⟩).1 k).val =
          (unmarkedFun n b i0 ⟨k.val - 1, by omega⟩).val + 1 :=
        markedFun_val_of_ge n _ i0 k h0 h1
      have hge : ¬ (⟨k.val - 1, by omega⟩ : Fin n).val < i0.val := h1
      have hU : (unmarkedFun n b i0 ⟨k.val - 1, by omega⟩).val =
          (b.1 ⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩).val - 1 :=
        unmarkedFun_val_of_ge n b i0 ⟨k.val - 1, by omega⟩ hge
      have heq : (⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩ :
          Fin (n + 1)) = k := by
        apply Fin.ext
        simp only
        omega
      have hleK : (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) ≤ k := by
        rw [Fin.le_def]
        simp only
        omega
      have hmon : b.1 ⟨i0.val + 1, by omega⟩ ≤ b.1 k := b.2.1 hleK
      have hfixV : (b.1 ⟨i0.val + 1, by omega⟩).val = i0.val + 1 :=
        congrArg Fin.val hfix
      have hle := Fin.le_def.mp hmon
      have hge1 : 1 ≤
          (b.1 ⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩).val := by
        rw [heq]
        omega
      rw [hL, hU, heq]
      omega

lemma sumToPark_surjective (n : ℕ) :
    Function.Surjective (sumToPark n) := by
  classical
  intro b
  by_cases h : ∃ k : Fin (n + 1), 0 < k.val ∧ b.1 k = k
  · obtain ⟨k_wit, hpos_wit, hfix_wit⟩ := h
    let S := Finset.univ.filter
      (fun k : Fin (n + 1) => 0 < k.val ∧ b.1 k = k)
    have hmem_wit : k_wit ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos_wit, hfix_wit⟩
    have hne : S.Nonempty := ⟨k_wit, hmem_wit⟩
    let k0 := S.min' hne
    have hk0_mem : k0 ∈ S := Finset.min'_mem _ _
    have hk0_filt := Finset.mem_filter.mp hk0_mem
    have hpos0 : 0 < k0.val := hk0_filt.2.1
    have hfix0 : b.1 k0 = k0 := hk0_filt.2.2
    have hmin_le : ∀ k ∈ S, k0 ≤ k :=
      fun k hk => Finset.min'_le _ _ hk
    let i0 : Fin n := ⟨k0.val - 1, by omega⟩
    have hi0_val : i0.val = k0.val - 1 := rfl
    have hFinEq : (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) = k0 := by
      apply Fin.ext
      simp only
      omega
    have hfix : b.1 ⟨i0.val + 1, by omega⟩ =
        ⟨i0.val + 1, by omega⟩ := by
      rw [hFinEq]
      exact hfix0
    have hmin : ∀ k : Fin (n + 1), 0 < k.val → k.val < i0.val + 1 →
        b.1 k ≠ k := by
      intro k hpos hlt heq
      have hk_mem : k ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos, heq⟩
      have hle := hmin_le k hk_mem
      have hleV := Fin.le_def.mp hle
      omega
    let m : Marked n :=
      ⟨⟨unmarkedFun n b i0, unmarkedFun_mono n b i0 hfix,
        fun j => unmarkedFun_bound n b i0 hmin j⟩,
        ⟨i0, unmarkedFun_fixed n b i0 hfix⟩⟩
    use Sum.inr m
    change embedMarked n m = b
    exact embedMarked_unmarked n b i0 hfix hmin
  · have hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k := by
      intro k hpos heq
      exact h ⟨k, hpos, heq⟩
    let a : Park n :=
      ⟨unplainFun n b hNo, unplainFun_mono n b hNo,
        fun j => unplainFun_bound n b hNo j⟩
    use Sum.inl a
    change embedPlain n a = b
    exact embedPlain_unplain n b hNo

lemma park_succ_card (n : ℕ) :
    Fintype.card (Park (n + 1)) =
      Fintype.card (Park n) + Fintype.card (Marked n) := by
  have hbij : Function.Bijective (sumToPark n) :=
    ⟨sumToPark_injective n, sumToPark_surjective n⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective (sumToPark n) hbij)
  rw [Fintype.card_sum] at hcard
  exact hcard.symm

lemma park_card_eq_catalan_aux : ∀ n m, m ≤ n →
    Fintype.card (Park m) = catalan m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    rw [park_zero_card, catalan_zero]
  | succ n ih =>
    intro m hm
    by_cases hmn : m ≤ n
    · exact ih m hmn
    · have hmeq : m = n + 1 := by omega
      subst hmeq
      have hPn : Fintype.card (Park n) = catalan n := ih n (Nat.le_refl n)
      have hPsucc := park_succ_card n
      have hM := marked_card_eq_fiber_sum n
      have hMsum : Fintype.card (Marked n) =
          ∑ i : Fin n, catalan i.val * catalan (n - i.val) := by
        rw [hM]
        apply Finset.sum_congr rfl
        intro i _
        have hi1 : i.val ≤ n := Nat.le_of_lt i.isLt
        have hi2 : n - i.val ≤ n := Nat.sub_le n i.val
        rw [ih _ hi1, ih _ hi2]
      have hcat := catalan_succ n
      have hsplit := Fin.sum_univ_castSucc
        (fun i : Fin (n + 1) => catalan i.val * catalan (n - i.val))
      have hcast_sum : (∑ i : Fin n,
          catalan (i.castSucc).val * catalan (n - (i.castSucc).val)) =
          ∑ i : Fin n, catalan i.val * catalan (n - i.val) :=
        Finset.sum_congr rfl (fun i _ => rfl)
      have hlast : catalan (Fin.last n).val *
          catalan (n - (Fin.last n).val) =
          catalan n := by
        have hnn : n - n = 0 := by omega
        have hdef : catalan (Fin.last n).val *
            catalan (n - (Fin.last n).val) =
            catalan n * catalan (n - n) := rfl
        rw [hdef, hnn, catalan_zero, mul_one]
      rw [hPsucc, hPn, hMsum]
      rw [hcat, hsplit, hcast_sum, hlast]
      exact add_comm _ _

lemma park_card_eq_catalan (n : ℕ) :
    Fintype.card (Park n) = catalan n :=
  park_card_eq_catalan_aux n n (Nat.le_refl n)

/--
The uniform average number of lucky cars/spots among weakly increasing
parking functions of length `n` is `3n / (n + 2)`. A weakly increasing
parking function is encoded 0-based as a monotone `a : Fin n → Fin n` with
`a i ≤ i`; the `i`-th car parks in spot `i` and is lucky exactly when
`a i = i`.

Source: Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens,
and Marshall Moats, "Lucky Cars and Lucky Spots in Parking Functions,"
Journal of Integer Sequences 29 (2026), Article 26.1.1, Corollary,
lines 631–633 (supporting lemma lines 619–629),
https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex
The corollary attributes the Dyck-path expectation value to Deutsch.

Proves `Wanted` entry `expected_lucky_spots_weakly_increasing_parking_functions`.
-/
theorem expected_lucky_spots_weakly_increasing_parking_functions
    (n : ℕ) (hn : 0 < n) :
    let parkingFunctions := Finset.univ.filter fun a : Fin n → Fin n =>
      Monotone a ∧ ∀ i, (a i).val ≤ i.val
    (∑ a ∈ parkingFunctions,
        ((Finset.univ.filter fun i : Fin n => a i = i).card : ℚ)) /
      (parkingFunctions.card : ℚ) = ((3 : ℚ) * n) / (n + 2) := by
  dsimp only
  have hPCardNat : (Finset.univ.filter fun a : Fin n → Fin n =>
      Monotone a ∧ ∀ i, (a i).val ≤ i.val).card =
      Fintype.card (Park n) := (park_card_eq_filter n).symm
  have hPCard : ((Finset.univ.filter fun a : Fin n → Fin n =>
      Monotone a ∧ ∀ i, (a i).val ≤ i.val).card : ℚ) =
      (Fintype.card (Park n) : ℚ) := congrArg Nat.cast hPCardNat
  have hMSum : (∑ a ∈ Finset.univ.filter fun a : Fin n → Fin n =>
      Monotone a ∧ ∀ i, (a i).val ≤ i.val,
      ((Finset.univ.filter fun i : Fin n => a i = i).card : ℚ)) =
      (Fintype.card (Marked n) : ℚ) := by
    rw [← Nat.cast_sum]
    exact congrArg Nat.cast (marked_card_eq_sum n).symm
  rw [hPCard, hMSum]
  have hCpos : 0 < catalan n := by
    have hcb := Nat.centralBinom_pos n
    have h1 := succ_mul_catalan_eq_centralBinom n
    have hpos : 0 < (n + 1) * catalan n := by
      rw [h1]
      exact hcb
    have hne : catalan n ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hpos
      exact lt_irrefl 0 hpos
    exact Nat.pos_of_ne_zero hne
  have hCn : 0 < Fintype.card (Park n) := by
    rw [park_card_eq_catalan n]
    exact hCpos
  have h1 : (n + 1) * Fintype.card (Park n) = n.centralBinom := by
    rw [park_card_eq_catalan n]
    exact succ_mul_catalan_eq_centralBinom n
  have h2 : (n + 2) * catalan (n + 1) = (n + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  have h3 : (n + 1) * (n + 1).centralBinom =
      2 * (2 * n + 1) * n.centralBinom :=
    Nat.succ_mul_centralBinom_succ n
  have hP1 : Fintype.card (Park (n + 1)) = catalan (n + 1) :=
    park_card_eq_catalan (n + 1)
  have hM' : catalan (n + 1) =
      Fintype.card (Park n) + Fintype.card (Marked n) := by
    rw [← hP1]
    exact park_succ_card n
  exact ratio_of_catalan n hn (Fintype.card (Park n)) hCn h1 h2 h3
    (Fintype.card (Marked n)) hM'

end MetaMathlibExt
end
