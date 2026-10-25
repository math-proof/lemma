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
import Def.NumberTheory.HilbertWaring.Part14
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

theorem hw_exists_powerFiber_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ M n : ℕ,
      #(hwPowerFiber k (8 ^ (k - 1)) M n) ≤
        C * (M + 1) ^ (8 ^ (k - 1) - k) := by
  obtain ⟨C, hC, hmoment⟩ := hw_exists_moment_bound k 1 hk
  refine ⟨C, hC, ?_⟩
  intro M n
  let s := 8 ^ (k - 1)
  let r := s / 2
  have hsEven : Even s := by
    rw [Nat.even_pow]
    exact ⟨by norm_num, by omega⟩
  have hrs : r + r = s := by
    have h := Nat.two_mul_div_two_of_even hsEven
    omega
  by_cases hM : M = 0
  · subst M
    calc
      #(hwPowerFiber k s 0 n) ≤
          #((Finset.univ : Finset (Fin s → Fin (0 + 1)))) := by
        exact Finset.card_filter_le _ _
      _ = 1 := by simp
      _ ≤ C * (0 + 1) ^ (s - k) := by simp; omega
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have htop : hwPowerCoeffs k ⟨k, by omega⟩ ≠ 0 := by
      simp [hwPowerCoeffs]
    have hmom := hmoment M (hwPowerCoeffs k) hMpos
      (hw_powerCoeffs_bound k M) htop
    have hpow : hwPolyEval k (hwPowerCoeffs k) = fun x : ℕ ↦ (x : ℤ) ^ k := by
      funext x
      exact hw_polyEval_power k x
    rw [hpow] at hmom
    calc
      #(hwPowerFiber k s M n) ≤
          #(hwSumFiber r M (fun x : ℕ ↦ (x : ℤ) ^ k) n) :=
        hw_powerFiber_card_le_sumFiber hrs
      _ ≤ #(hwMomentFinset r M (fun x : ℕ ↦ (x : ℤ) ^ k)) :=
        hw_sumFiber_card_le_moment r M _ n
      _ ≤ C * M ^ (s - k) := by
        simpa only [s, r] using hmom
      _ ≤ C * (M + 1) ^ (s - k) :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) (s - k))

end MathlibExt.NumberTheory.HilbertWaringWanted
