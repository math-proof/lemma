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
import Def.NumberTheory.HilbertWaring.Part7
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

lemma hw_quadratic_moment_bound (c : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (N : ℕ) (a : Fin 3 → ℤ), 0 < N →
      hwCoeffBound 2 c N a → a 2 ≠ 0 →
        #(hwMomentFinset 4 N (hwPolyEval 2 a)) ≤ C * N ^ 6 := by
  obtain ⟨C₀, hC₀, hfour⟩ := hw_exists_fourTermCount_bound
  let D := 3 * c
  let E := 2 * D + 1
  let C := C₀ * D ^ 3 + E ^ 4 + 108 * E ^ 3
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N a hN ha ha₂
  have hc : 0 < c := by
    have hbound := ha (2 : Fin 3)
    have hpos := Int.natAbs_pos.mpr ha₂
    norm_num at hbound
    omega
  have hD : 0 < D := by dsimp [D]; positivity
  have hNM : N ≤ D * N := by
    apply Nat.le_mul_of_pos_left
    exact hD
  have htwoN : 2 * N + 1 ≤ 3 * N := by omega
  have htwoM : 2 * (D * N) + 1 ≤ E * N := by
    rw [show E * N = 2 * (D * N) + N by dsimp [E]; ring]
    omega
  have hfour' : hwFourTermCount N (D * N) ≤ C₀ * D ^ 3 * N ^ 6 := by
    calc
      hwFourTermCount N (D * N) ≤ C₀ * (N * (D * N)) ^ 3 :=
        hfour N (D * N) hN hNM
      _ = C₀ * D ^ 3 * N ^ 6 := by ring
  have hquartic : (2 * (D * N) + 1) ^ 4 ≤ E ^ 4 * N ^ 6 := by
    calc
      (2 * (D * N) + 1) ^ 4 ≤ (E * N) ^ 4 := Nat.pow_le_pow_left htwoM 4
      _ = E ^ 4 * N ^ 4 := by ring
      _ ≤ E ^ 4 * N ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by omega))
  have hcubic : 4 * (2 * N + 1) ^ 3 * (2 * (D * N) + 1) ^ 3 ≤
      108 * E ^ 3 * N ^ 6 := by
    calc
      4 * (2 * N + 1) ^ 3 * (2 * (D * N) + 1) ^ 3 ≤
          4 * (3 * N) ^ 3 * (E * N) ^ 3 := by
        gcongr
      _ = 108 * E ^ 3 * N ^ 6 := by ring
  have hcenter := hw_centeredFourTerm_card_le N (D * N)
  have hcenter' : #(hwCenteredFourTerm N (D * N)) ≤ C * N ^ 6 := by
    calc
      #(hwCenteredFourTerm N (D * N)) ≤
          hwFourTermCount N (D * N) + (2 * (D * N) + 1) ^ 4 +
            4 * (2 * N + 1) ^ 3 * (2 * (D * N) + 1) ^ 3 := hcenter
      _ ≤ C₀ * D ^ 3 * N ^ 6 + E ^ 4 * N ^ 6 + 108 * E ^ 3 * N ^ 6 :=
        Nat.add_le_add (Nat.add_le_add hfour' hquartic) hcubic
      _ = C * N ^ 6 := by dsimp [C]; ring
  calc
    #(hwMomentFinset 4 N (hwPolyEval 2 a)) ≤
        #(hwCenteredFourTerm N (3 * c * N)) :=
      hw_quadratic_moment_le_centered c N a ha ha₂
    _ = #(hwCenteredFourTerm N (D * N)) := by rfl
    _ ≤ C * N ^ 6 := hcenter'

end MathlibExt.NumberTheory.HilbertWaringWanted
