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
import Theorem.NumberTheory.HilbertWaring.Part2
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

def hwCenteredToSigned
    (H : ℕ) (x : {x : Fin (2 * H + 1) // hwCentered H x ≠ 0}) : hwSigned H :=
  if hx : H < x.1.val then
    (0, ⟨x.1.val - H - 1, by omega⟩)
  else
    (1, ⟨H - x.1.val - 1, by
      have hne : x.1.val ≠ H := by
        intro h
        apply x.2
        simp [hwCentered, h]
      omega⟩)

def hwSignedEquivCentered (H : ℕ) :
    hwSigned H ≃ {x : Fin (2 * H + 1) // hwCentered H x ≠ 0} where
  toFun h := ⟨hwSignedToCentered H h, by
    rw [hw_centered_signedToCentered]
    exact hw_signedVal_ne_zero H h⟩
  invFun := hwCenteredToSigned H
  left_inv h := by
    rcases h with ⟨s, i⟩
    fin_cases s
    · apply Prod.ext
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered]
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered]
    · have hi := i.isLt
      have hnot : ¬H < H - (i.val + 1) := by omega
      apply Prod.ext
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered, hnot]
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered, hnot]
        omega
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    by_cases hx : H < x.1.val
    · simp [hwCenteredToSigned, hwSignedToCentered, hx]
      omega
    · have hne : x.1.val ≠ H := by
        intro h
        apply x.2
        simp [hwCentered, h]
      simp [hwCenteredToSigned, hwSignedToCentered, hx]
      omega

def hwLinearFiber (M : ℕ) (c : Fin 4 → ℤ) :
    Finset (Fin 4 → Fin (2 * M + 1)) :=
  Finset.univ.filter fun m ↦ ∑ i, c i * hwCentered M (m i) = 0

def hwCoordZero (H : ℕ) (i : Fin 4) :
    Finset (Fin 4 → Fin (2 * H + 1)) :=
  Finset.univ.filter fun h ↦ hwCentered H (h i) = 0

def hwHasZero (H : ℕ) : Finset (Fin 4 → Fin (2 * H + 1)) :=
  Finset.univ.filter fun h ↦ ∃ i, hwCentered H (h i) = 0

end MathlibExt.NumberTheory.HilbertWaringWanted
