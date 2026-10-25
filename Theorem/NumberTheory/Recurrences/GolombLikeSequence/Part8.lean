/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.PNat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Def.NumberTheory.Recurrences.GolombLikeSequence.Part8
/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/


namespace MetaMathlibExt

theorem glk_v_one
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    glk_v y z hy hz 1 = glk_c y z + 1 := by
  have hsum : 2 ≤ y + z := by omega
  have hv := glk_v_of_mem y z hy hz 1 0 (by simp [glk_l]) (by simp [glk_l]; omega)
  have hc := glk_c_spec y z hz hpar
  rw [hv]
  have hleft : (1 : ℤ) < glk_a y z 0 := by
    simp [glk_a, glk_l]
    omega
  simp [glk_a, glk_l]
  omega

theorem glk_f_seq_step
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (n : ℕ) :
    glk_seq (glk_f y z hy hz hpar) (n + 1) =
        glk_seq (glk_f y z hy hz hpar) n + 1 ∨
      glk_seq (glk_f y z hy hz hpar) (n + 1) =
        glk_seq (glk_f y z hy hz hpar) n + y.toNat := by
  have hs := glk_v_step y z hy hz hpar ((n : ℤ) + 1) (by omega)
  have hn := glk_f_val y z hy hz hpar n.succPNat
  have hn1 := glk_f_val y z hy hz hpar (n + 1).succPNat
  have hycast : (↑y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
  norm_num [glk_seq] at hn hn1
  rcases hs with hs | hs
  · left
    apply Int.ofNat_inj.mp
    simp only [glk_seq]
    push_cast
    rw [hn, hn1]
    exact hs
  · right
    apply Int.ofNat_inj.mp
    simp only [glk_seq]
    push_cast
    rw [hn, hn1, hycast]
    exact hs

theorem glk_f_strictMono
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    StrictMono (glk_f y z hy hz hpar) := by
  apply glk_strict_of_seq_strict
  apply strictMono_nat_of_lt_succ
  intro n
  rcases glk_f_seq_step y z hy hz hpar n with h | h
  · omega
  · have hycast : (↑y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hyNat : 2 ≤ y.toNat := by omega
    omega

theorem glk_f_one
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    (↑((glk_f y z hy hz hpar 1).val) : ℤ) = glk_c y z + 1 := by
  calc
    (↑((glk_f y z hy hz hpar 1).val) : ℤ) = glk_v y z hy hz 1 := by
      simpa using glk_f_val y z hy hz hpar (1 : ℕ+)
    _ = glk_c y z + 1 := glk_v_one y z hy hz hpar

theorem glk_f_comp
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (n : ℕ+) :
    (↑((glk_f y z hy hz hpar (glk_f y z hy hz hpar n)).val) : ℤ) =
      y * (↑n.val : ℤ) + z := by
  calc
    (↑((glk_f y z hy hz hpar (glk_f y z hy hz hpar n)).val) : ℤ) =
        glk_v y z hy hz (↑((glk_f y z hy hz hpar n).val) : ℤ) :=
      glk_f_val y z hy hz hpar _
    _ = glk_v y z hy hz (glk_v y z hy hz n.val) := by
      rw [glk_f_val y z hy hz hpar n]
    _ = y * (↑n.val : ℤ) + z :=
      glk_v_comp y z hy hz hpar n.val (by exact_mod_cast n.pos)

theorem glk_initial_int
    (y z : ℤ) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (f : ℕ+ → ℕ+)
    (hone : (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2) :
    (↑((f 1).val) : ℤ) = glk_c y z + 1 := by
  have hc := (glk_c_spec y z hz hpar).2
  have hrat : ((y : ℚ) + (z : ℚ) + 1) / 2 = (glk_c y z : ℚ) + 1 := by
    apply (div_eq_iff (by norm_num : (2 : ℚ) ≠ 0)).2
    exact_mod_cast (by omega : y + z + 1 = (glk_c y z + 1) * 2)
  rw [hrat] at hone
  exact_mod_cast hone

theorem glk_seq_comp
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (f : ℕ+ → ℕ+)
    (hcomp : ∀ n : ℕ+, (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z)
    (n : ℕ) :
    glk_seq f (glk_seq f n - 1) =
      y.toNat * n + 2 * (glk_c y z).toNat + 1 := by
  have hc := glk_c_spec y z hz hpar
  have hycast : (↑y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
  have hccast : (↑(glk_c y z).toNat : ℤ) = glk_c y z :=
    Int.toNat_of_nonneg (by omega)
  have hrec := hcomp n.succPNat
  have hleft : (↑(glk_seq f (glk_seq f n - 1)) : ℤ) =
      y * ((n : ℤ) + 1) + z := by
    have hp : (glk_seq f n - 1).succPNat = f n.succPNat := by
      change ((f n.succPNat).val - 1).succPNat = f n.succPNat
      exact PNat.succPNat_natPred _
    change (↑((f (glk_seq f n - 1).succPNat).val) : ℤ) =
      y * ((n : ℤ) + 1) + z
    rw [hp]
    simpa using hrec
  apply Int.ofNat_inj.mp
  push_cast
  rw [hleft, hycast, hccast]
  ring_nf
  omega

theorem glk_f_unique
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (f : ℕ+ → ℕ+) (hf : StrictMono f)
    (hone : (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2)
    (hcomp : ∀ n : ℕ+, (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z) :
    f = glk_f y z hy hz hpar := by
  let C := (glk_c y z).toNat
  let Y := y.toNat
  have hc := glk_c_spec y z hz hpar
  have hCcast : (↑C : ℤ) = glk_c y z := Int.toNat_of_nonneg (by omega)
  have hYcast : (↑Y : ℤ) = y := Int.toNat_of_nonneg (by omega)
  have hC : 1 ≤ C := by omega
  have hY : 2 ≤ Y := by omega
  have hf0int := glk_initial_int y z hz hpar f hone
  have hF0int := glk_f_one y z hy hz hpar
  have hf0 := glk_seq_zero_of_initial_int y z f hf0int
  have hF0 := glk_seq_zero_of_initial_int y z (glk_f y z hy hz hpar) hF0int
  change glk_seq f 0 = C + 1 at hf0
  change glk_seq (glk_f y z hy hz hpar) 0 = C + 1 at hF0
  have hseq := glk_unique_seq C Y hC hY
    (glk_seq (glk_f y z hy hz hpar)) (glk_seq f)
    (glk_seq_strict_of_strict _ (glk_f_strictMono y z hy hz hpar))
    (glk_seq_strict_of_strict f hf) hF0 hf0
    (by
      intro n
      exact glk_seq_comp y z hy hz hpar _ (glk_f_comp y z hy hz hpar) n)
    (by
      intro n
      exact glk_seq_comp y z hy hz hpar f hcomp n)
    (glk_f_seq_step y z hy hz hpar)
  funext n
  have hn := congrFun hseq n.natPred
  simpa [glk_seq] using hn

theorem glk_block_formula
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (k : ℕ) (j : ℤ)
    (hlow : -(glk_c y z * y ^ k) ≤ j) (hupp : j < glk_c y z * y ^ k) :
    ∃ m : ℕ+,
      (↑m.val : ℤ) = glk_a y z k + j ∧
      (↑((glk_f y z hy hz hpar m).val) : ℤ) =
        glk_l y z (k + 1) + if j < 0 then j else y * j := by
  have hnext := glk_l_succ_eq_a_add y z hz hpar k
  have hxlow : glk_l y z k ≤ glk_a y z k + j := by
    unfold glk_a at hnext ⊢
    nlinarith
  have hxupp : glk_a y z k + j < glk_l y z (k + 1) := by omega
  have hxpos : 0 < glk_a y z k + j :=
    lt_of_lt_of_le Int.zero_lt_one (le_trans (glk_l_one_le y z hy hz k) hxlow)
  let m := glk_toPNat (glk_a y z k + j) hxpos
  refine ⟨m, glk_toPNat_val _ _, ?_⟩
  rw [glk_f_val]
  rw [glk_toPNat_val, glk_v_of_mem y z hy hz _ k hxlow hxupp]
  by_cases hj : j < 0
  · simp [hj]
    ring
  · simp [hj]

theorem glk_c_rat
    (y z : ℤ) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    (glk_c y z : ℚ) = ((y : ℚ) + (z : ℚ) - 1) / 2 := by
  apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).2
  exact_mod_cast (by
    have hc := (glk_c_spec y z hz hpar).2
    omega : glk_c y z * 2 = y + z - 1)

theorem glk_a_rat
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (k : ℕ) :
    (glk_a y z k : ℚ) =
      (((y : ℚ) + 1) * ((y : ℚ) + (z : ℚ) - 1) /
        (2 * ((y : ℚ) - 1))) * (y : ℚ) ^ k -
        (z : ℚ) / ((y : ℚ) - 1) := by
  have hden : (y : ℚ) - 1 ≠ 0 := by exact_mod_cast (by omega : y - 1 ≠ 0)
  rw [glk_a]
  push_cast
  rw [glk_l_rat y z hy k]
  have hc := glk_c_rat y z hz hpar
  rw [hc]
  field_simp [hden]
  ring

theorem glk_closed_form
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (k : ℕ) (j : ℤ)
    (hlow : -(((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k ≤ (j : ℚ))
    (hupp : (j : ℚ) < (((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k) :
    ∃ m : ℕ+,
      (↑m.val : ℚ) =
          (((y : ℚ) + 1) * ((y : ℚ) + (z : ℚ) - 1) /
            (2 * ((y : ℚ) - 1))) *
            (y : ℚ) ^ k -
          (z : ℚ) / ((y : ℚ) - 1) + (j : ℚ) ∧
      (↑((glk_f y z hy hz hpar m).val) : ℚ) =
          (((y : ℚ) + (z : ℚ) - 1) / ((y : ℚ) - 1)) *
            (y : ℚ) ^ (k + 1) -
          (z : ℚ) / ((y : ℚ) - 1) +
          ((y : ℚ) + 1) * (j : ℚ) / 2 +
          ((y : ℚ) - 1) * |(j : ℚ)| / 2 := by
  have hcq := glk_c_rat y z hz hpar
  have hlowInt : -(glk_c y z * y ^ k) ≤ j := by
    rw [← hcq] at hlow
    have h : -glk_c y z * y ^ k ≤ j := by exact_mod_cast hlow
    simpa only [neg_mul] using h
  have huppInt : j < glk_c y z * y ^ k := by
    rw [← hcq] at hupp
    exact_mod_cast hupp
  obtain ⟨m, hm, hfm⟩ := glk_block_formula y z hy hz hpar k j hlowInt huppInt
  refine ⟨m, ?_, ?_⟩
  · have hmQ : (↑m.val : ℚ) = (glk_a y z k : ℚ) + (j : ℚ) := by
      exact_mod_cast hm
    rw [glk_a_rat y z hy hz hpar k] at hmQ
    exact hmQ
  · have hfmQ : (↑((glk_f y z hy hz hpar m).val) : ℚ) =
        (glk_l y z (k + 1) : ℚ) +
          if j < 0 then (j : ℚ) else (y : ℚ) * (j : ℚ) := by
      by_cases hj : j < 0
      · rw [ite_eq_left hj]
        simp only [hj, ↓reduceIte] at hfm
        exact_mod_cast hfm
      · rw [ite_eq_right hj]
        simp only [hj, ↓reduceIte] at hfm
        exact_mod_cast hfm
    rw [glk_l_rat y z hy (k + 1), glk_offset_rat y j] at hfmQ
    simpa only [add_assoc] using hfmQ

theorem glk_f_one_rat
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    (↑((glk_f y z hy hz hpar 1).val) : ℚ) =
      ((y : ℚ) + (z : ℚ) + 1) / 2 := by
  have hInt := glk_f_one y z hy hz hpar
  have hRat : (↑((glk_f y z hy hz hpar 1).val) : ℚ) =
      (glk_c y z : ℚ) + 1 := by
    exact_mod_cast hInt
  rw [glk_c_rat y z hz hpar] at hRat
  calc
    (↑((glk_f y z hy hz hpar 1).val) : ℚ) =
        ((y : ℚ) + (z : ℚ) - 1) / 2 + 1 := hRat
    _ = ((y : ℚ) + (z : ℚ) + 1) / 2 := by ring

/--
Closed form for Golomb-like solutions of `f (f n) = y * n + z`.

Source: Benoit Cloitre, N. J. A. Sloane, and Matthew J. Vandermast,
"Numerical Analogues of Aronson's Sequence," Journal of Integer
Sequences 6 (2003), Article 03.2.2, Theorem (label Th1), equations
(Eq48a) and (Eq48), lines 584–603,
https://cs.uwaterloo.ca/journals/JIS/VOL6/Cloitre/cloitre2.tex

The source's opposite-parity hypothesis is `y % 2 ≠ z % 2`; the
constants `c_1` and `c_2` of the source are expanded inline.

Proves `Wanted` entry `golomb_like_closed_form`.

Proof: The construction tiles the positive integers by the source's blocks and verifies the
two slope regimes, followed by strong-induction uniqueness, as in Cloitre–Sloane–Vandermast,
Theorem Th1 and equations (Eq48a), (Eq48).
-/
theorem golomb_like_closed_form
    (y z : ℤ)
    (hy : 2 ≤ y)
    (hz : 2 - y ≤ z)
    (hpar : y % 2 ≠ z % 2) :
    (∃! f : ℕ+ → ℕ+,
      StrictMono f ∧
      (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2 ∧
      ∀ n : ℕ+,
        (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z) ∧
    ∀ f : ℕ+ → ℕ+,
      StrictMono f →
      (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2 →
      (∀ n : ℕ+,
        (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z) →
      ∀ k : ℕ, ∀ j : ℤ,
        -(((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k ≤ (j : ℚ) →
        (j : ℚ) < (((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k →
        ∃ m : ℕ+,
          (↑m.val : ℚ) =
              (((y : ℚ) + 1) * ((y : ℚ) + (z : ℚ) - 1) /
                (2 * ((y : ℚ) - 1))) *
                (y : ℚ) ^ k -
              (z : ℚ) / ((y : ℚ) - 1) + (j : ℚ) ∧
          (↑((f m).val) : ℚ) =
              (((y : ℚ) + (z : ℚ) - 1) / ((y : ℚ) - 1)) *
                (y : ℚ) ^ (k + 1) -
              (z : ℚ) / ((y : ℚ) - 1) +
              ((y : ℚ) + 1) * (j : ℚ) / 2 +
              ((y : ℚ) - 1) * |(j : ℚ)| / 2 := by
  constructor
  · refine ⟨glk_f y z hy hz hpar, ?_, ?_⟩
    · exact ⟨glk_f_strictMono y z hy hz hpar, glk_f_one_rat y z hy hz hpar,
        glk_f_comp y z hy hz hpar⟩
    · intro f hf
      exact glk_f_unique y z hy hz hpar f hf.1 hf.2.1 hf.2.2
  · intro f hf hone hcomp k j hlow hupp
    rw [glk_f_unique y z hy hz hpar f hf hone hcomp]
    exact glk_closed_form y z hy hz hpar k j hlow hupp

end MetaMathlibExt
