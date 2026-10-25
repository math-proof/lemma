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
import Def.NumberTheory.HilbertWaring.Part12
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

lemma hw_step_zero_count_bound (k c Cᵢ C₄ N : ℕ) (hk : 3 ≤ k)
    (hN : 0 < N) (a : Fin (k + 1) → ℤ) (ha : hwCoeffBound k c N a)
    (haTop : a ⟨k, by omega⟩ ≠ 0)
    (hI : ∀ (N : ℕ) (b : Fin (k - 1 + 1) → ℤ), 0 < N →
      hwCoeffBound (k - 1) (hwStepD k c) N b → b ⟨k - 1, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 2) / 2) N (hwPolyEval (k - 1) b)) ≤
        Cᵢ * N ^ (8 ^ (k - 2) - (k - 1)))
    (hfour : ∀ H M : ℕ, 0 < H → H ≤ M →
      hwFourTermCount H M ≤ C₄ * (H * M) ^ 3) :
    #(hwZeroQuadruples
        (hwBlockChoiceFreq k (hwStepR k) N (by omega) a)) ≤
      (C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4) *
        N ^ (8 * hwStepR k - k + 4) := by
  let r := hwStepR k
  let D := hwStepD k c
  let V := hwStepV k c N
  let M := hwStepM k c N
  let A := Cᵢ * N ^ (2 * r - (k - 1))
  have hrel := hw_step_pow_relations k hk
  have hdegree := (hw_step_degree_bounds k hk).1
  have hm : ∀ z : hwBlockChoice r N,
      (hwBlockChoiceDiff k r N (by omega) a z).natAbs ≤ M := by
    intro z
    have hz := hw_blockChoiceDiff_natAbs_le k c r N (by omega) a ha z
    apply hz.trans
    change 2 * r * V ≤ M
    exact le_max_right _ _
  have hA : ∀ h : hwSigned N,
      #(hwMomentFinset r N
        (hwPolyEval (k - 1) (hwDiffCoeffs k (by omega) a (h.2.val + 1)))) ≤ A := by
    intro h
    have hh : h.2.val + 1 ≤ N := by omega
    have hcoeff : hwCoeffBound (k - 1) D N
        (hwDiffCoeffs k (by omega) a (h.2.val + 1)) := by
      simpa [D, hwStepD] using
        hw_diffCoeffs_bound k c N (h.2.val + 1) (by omega) hh a ha
    have htop : (hwDiffCoeffs k (by omega) a (h.2.val + 1)) ⟨k - 1, by omega⟩ =
        (k : ℤ) * a ⟨k, by omega⟩ := by
      simpa [hwDiffCoeffs] using
        hw_diffCoeff_top k (h.2.val + 1) (by omega) a
    have htopne : (hwDiffCoeffs k (by omega) a (h.2.val + 1))
        ⟨k - 1, by omega⟩ ≠ 0 := by
      rw [htop]
      exact mul_ne_zero (by exact_mod_cast (show k ≠ 0 by omega)) haTop
    have hi := hI N (hwDiffCoeffs k (by omega) a (h.2.val + 1)) hN hcoeff htopne
    change #(hwMomentFinset r N
      (hwPolyEval (k - 1) (hwDiffCoeffs k (by omega) a (h.2.val + 1)))) ≤ A
    dsimp [A, r]
    rw [hrel.2.2.2, ← hrel.1] at hi
    exact hi
  have hzero := hw_zeroQuadruples_card_le k r N M A (by omega) a hm hA
  have hM := hw_stepM_bounds k c N hk hN
  have hfour' : hwFourTermCount N M ≤
      C₄ * hwStepE k c ^ 3 * N ^ (3 * k) := by
    have hpow : N * N ^ (k - 1) = N ^ k := by
      calc
        N * N ^ (k - 1) = N ^ (k - 1) * N := by ac_rfl
        _ = N ^ ((k - 1) + 1) := (pow_succ N (k - 1)).symm
        _ = N ^ k := by
          congr 2
          all_goals omega
    have hNM : N * M ≤ hwStepE k c * N ^ k := by
      calc
        N * M ≤ N * (hwStepE k c * N ^ (k - 1)) :=
          Nat.mul_le_mul_left N hM.2
        _ = hwStepE k c * N ^ k := by
          rw [← hpow]
          ring
    calc
      hwFourTermCount N M ≤ C₄ * (N * M) ^ 3 := hfour N M hN hM.1
      _ ≤ C₄ * (hwStepE k c * N ^ k) ^ 3 := by gcongr
      _ = C₄ * hwStepE k c ^ 3 * N ^ (3 * k) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm k 3]
        ring
  have hA₄ : A ^ 4 = Cᵢ ^ 4 * N ^ (4 * (2 * r - (k - 1))) := by
    dsimp [A]
    rw [mul_pow, ← pow_mul, Nat.mul_comm (2 * r - (k - 1)) 4]
  calc
    #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a)) ≤
        hwFourTermCount N M * A ^ 4 := hzero
    _ = hwFourTermCount N M *
        (Cᵢ ^ 4 * N ^ (4 * (2 * r - (k - 1)))) := by rw [hA₄]
    _ ≤ (C₄ * hwStepE k c ^ 3 * N ^ (3 * k)) *
        (Cᵢ ^ 4 * N ^ (4 * (2 * r - (k - 1)))) := by
      exact Nat.mul_le_mul_right _ hfour'
    _ = (C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4) *
        N ^ (3 * k + 4 * (2 * r - (k - 1))) := by
      rw [pow_add]
      ring
    _ = (C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4) *
        N ^ (8 * r - k + 4) := by
      congr 2
      omega

end MathlibExt.NumberTheory.HilbertWaringWanted
