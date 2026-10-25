/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Def.Combinatorics.Schnirelmann
import Lemma.Finset.Schnirelmann
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
import Def.NumberTheory.HilbertWaring.Part13
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

lemma hw_moment_induction_step (k c Cᵢ C₄ : ℕ) (hk : 3 ≤ k)
    (hI : ∀ (N : ℕ) (b : Fin (k - 1 + 1) → ℤ), 0 < N →
      hwCoeffBound (k - 1) (hwStepD k c) N b → b ⟨k - 1, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 2) / 2) N (hwPolyEval (k - 1) b)) ≤
        Cᵢ * N ^ (8 ^ (k - 2) - (k - 1)))
    (hfour : ∀ H M : ℕ, 0 < H → H ≤ M →
      hwFourTermCount H M ≤ C₄ * (H * M) ^ 3) :
    ∀ (N : ℕ) (a : Fin (k + 1) → ℤ), 0 < N →
      hwCoeffBound k c N a → a ⟨k, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 1) / 2) N (hwPolyEval k a)) ≤
        hwStepC k c Cᵢ C₄ * N ^ (8 ^ (k - 1) - k) := by
  intro N a hN ha haTop
  let r := hwStepR k
  let M := hwStepM k c N
  let Vₑ := (k + 1) * c * N ^ k
  let P := max (2 * (8 * r) * Vₑ) (4 * N * M) + 1
  let K := hwStepK k c Cᵢ C₄
  let C := hwStepC k c Cᵢ C₄
  let _ : NeZero P := ⟨by simp [P]⟩
  have hrel := hw_step_pow_relations k hk
  have hdegrees := hw_step_degree_bounds k hk
  have hr : 0 < r := by
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hm : ∀ z : hwBlockChoice r N,
      (hwBlockChoiceDiff k r N (by omega) a z).natAbs ≤ M := by
    intro z
    have hz := hw_blockChoiceDiff_natAbs_le k c r N (by omega) a ha z
    apply hz.trans
    change 2 * r * hwStepV k c N ≤ M
    exact le_max_right _ _
  have hf : ∀ n ≤ N, (hwPolyEval k a n).natAbs ≤ Vₑ := by
    intro n hn
    simpa [Vₑ, mul_assoc] using hw_polyEval_natAbs_le k c N n hn a ha
  have hPmoment : 2 * (8 * r) * Vₑ < P := by
    dsimp [P]
    exact (le_max_left _ _).trans_lt (Nat.lt_succ_self _)
  have hPblock : 4 * N * M < P := by
    dsimp [P]
    exact (le_max_right _ _).trans_lt (Nat.lt_succ_self _)
  have hmoment := hw_real_character_moment_eq_card_of_lt
    P (8 * r) N Vₑ (hwPolyEval k a) hf hPmoment
  have hblock := hw_block_fourth_sum_eq_zero_count_of_lt
    P k r N M (by omega) a hm hPblock
  have hzero := hw_step_zero_count_bound k c Cᵢ C₄ N hk hN a ha haTop hI hfour
  have hpoint :
      (∑ α : ZMod P, ‖hwWeylSum P N (hwPolyEval k a) α‖ ^ (16 * r)) ≤
        ∑ α : ZMod P, 2 ^ (8 * r) *
          (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
            ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
              (∑ h : hwSigned N,
                ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4) := by
    apply Finset.sum_le_sum
    intro α _
    exact hw_weyl_pointwise_le P k r N hr a α
  have hsum :
      (∑ α : ZMod P, 2 ^ (8 * r) *
        (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
          ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
            (∑ h : hwSigned N,
              ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4)) =
        (P : ℝ) * 2 ^ (8 * r) *
          (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
            ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
              #(hwZeroQuadruples
                (hwBlockChoiceFreq k r N (by omega) a))) := by
    calc
      _ = (∑ _α : ZMod P,
            (2 ^ (8 * r) : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (8 * r)) +
          ∑ α : ZMod P,
            (2 ^ (8 * r) : ℝ) * (((2 * N : ℕ) : ℝ) ^ (8 * r - 4)) *
              (∑ h : hwSigned N,
                ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro α _
        push_cast
        ring
      _ = (P : ℝ) * ((2 ^ (8 * r) : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (8 * r))) +
          ((2 ^ (8 * r) : ℝ) * (((2 * N : ℕ) : ℝ) ^ (8 * r - 4))) *
            ∑ α : ZMod P, (∑ h : hwSigned N,
              ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4 := by
        rw [Finset.mul_sum]
        simp [ZMod.card]
      _ = _ := by
        rw [hblock]
        push_cast
        ring
  have hdiag : (((N + 1 : ℕ) : ℝ) ^ (8 * r)) ≤
      2 ^ (8 * r) * (N : ℝ) ^ (16 * r - k) := by
    have hNtwo : N + 1 ≤ 2 * N := by omega
    have hexp : 8 * r ≤ 16 * r - k := by omega
    calc
      (((N + 1 : ℕ) : ℝ) ^ (8 * r)) ≤
          (((2 * N : ℕ) : ℝ) ^ (8 * r)) := by
        exact_mod_cast (Nat.pow_le_pow_left hNtwo (8 * r))
      _ = 2 ^ (8 * r) * (N : ℝ) ^ (8 * r) := by
        push_cast
        rw [mul_pow]
      _ ≤ 2 ^ (8 * r) * (N : ℝ) ^ (16 * r - k) := by
        have hpN : N ^ (8 * r) ≤ N ^ (16 * r - k) :=
          Nat.pow_le_pow_right hN hexp
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast hpN
        · positivity
  have hblockNat :
      (2 * N) ^ (8 * r - 4) *
          #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a)) ≤
        2 ^ (8 * r - 4) * K * N ^ (16 * r - k) := by
    calc
      (2 * N) ^ (8 * r - 4) *
          #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a)) ≤
        (2 * N) ^ (8 * r - 4) * (K * N ^ (8 * r - k + 4)) := by
          gcongr
          simpa [K, hwStepK] using hzero
      _ = 2 ^ (8 * r - 4) * K * N ^ (16 * r - k) := by
        rw [mul_pow]
        calc
          2 ^ (8 * r - 4) * N ^ (8 * r - 4) *
              (K * N ^ (8 * r - k + 4)) =
            2 ^ (8 * r - 4) * K *
              (N ^ (8 * r - 4) * N ^ (8 * r - k + 4)) := by ring
          _ = _ := by
            rw [← pow_add]
            congr 3
            omega
  have hbracket :
      (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
        ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
          #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a))) ≤
      (2 ^ (8 * r) + 2 ^ (8 * r - 4) * K) *
        (N : ℝ) ^ (16 * r - k) := by
    calc
      _ ≤ 2 ^ (8 * r) * (N : ℝ) ^ (16 * r - k) +
          (2 ^ (8 * r - 4) * K : ℕ) * (N : ℝ) ^ (16 * r - k) := by
        exact add_le_add hdiag (by exact_mod_cast hblockNat)
      _ = _ := by push_cast; ring
  have hPpos : (0 : ℝ) < P := Nat.cast_pos.mpr (NeZero.pos P)
  have hcancel : (#(hwMomentFinset (8 * r) N (hwPolyEval k a)) : ℝ) ≤
      C * N ^ (16 * r - k) := by
    apply le_of_mul_le_mul_left (a := (P : ℝ)) _ hPpos
    calc
      (P : ℝ) * #(hwMomentFinset (8 * r) N (hwPolyEval k a)) =
          ∑ α : ZMod P,
            ‖hwWeylSum P N (hwPolyEval k a) α‖ ^ (16 * r) := by
        rw [← show 2 * (8 * r) = 16 * r by omega]
        exact hmoment.symm
      _ ≤ _ := hpoint
      _ = (P : ℝ) * 2 ^ (8 * r) *
          (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
            ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
              #(hwZeroQuadruples
                (hwBlockChoiceFreq k r N (by omega) a))) := hsum
      _ ≤ (P : ℝ) * 2 ^ (8 * r) *
          ((2 ^ (8 * r) + 2 ^ (8 * r - 4) * K) *
            (N : ℝ) ^ (16 * r - k)) := by gcongr
      _ = (P : ℝ) * (C * N ^ (16 * r - k)) := by
        simp [C, hwStepC, K]
        ring
  have hnat : #(hwMomentFinset (8 * r) N (hwPolyEval k a)) ≤
      C * N ^ (16 * r - k) := by exact_mod_cast hcancel
  dsimp [C, r] at hnat ⊢
  rw [← hrel.2.1, ← hrel.2.2.1]
  exact hnat

theorem hw_exists_moment_bound (k c : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ (N : ℕ) (a : Fin (k + 1) → ℤ), 0 < N →
      hwCoeffBound k c N a → a ⟨k, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 1) / 2) N (hwPolyEval k a)) ≤
        C * N ^ (8 ^ (k - 1) - k) := by
  revert c
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro c
      by_cases hk₂ : k = 2
      · subst k
        simpa using hw_quadratic_moment_bound c
      · have hk₃ : 3 ≤ k := by omega
        obtain ⟨Cᵢ, _, hI₀⟩ :=
          ih (k - 1) (by omega) (by omega) (hwStepD k c)
        obtain ⟨C₄, _, hfour⟩ := hw_exists_fourTermCount_bound
        let C := hwStepC k c Cᵢ C₄
        have hI : ∀ (N : ℕ) (b : Fin (k - 1 + 1) → ℤ), 0 < N →
            hwCoeffBound (k - 1) (hwStepD k c) N b →
              b ⟨k - 1, by omega⟩ ≠ 0 →
            #(hwMomentFinset (8 ^ (k - 2) / 2) N (hwPolyEval (k - 1) b)) ≤
              Cᵢ * N ^ (8 ^ (k - 2) - (k - 1)) := by
          intro N b hN hb hbtop
          have hi := hI₀ N b hN hb hbtop
          rw [show k - 1 - 1 = k - 2 by omega] at hi
          exact hi
        refine ⟨C, ?_, ?_⟩
        · dsimp [C, hwStepC]
          exact Nat.mul_pos (pow_pos (by omega) _)
            (Nat.add_pos_left (pow_pos (by omega) _) _)
        · exact hw_moment_induction_step k c Cᵢ C₄ hk₃ hI hfour

end MathlibExt.NumberTheory.HilbertWaringWanted
