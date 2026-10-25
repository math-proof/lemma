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
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

def hwCentered (M : ℕ) (x : Fin (2 * M + 1)) : ℤ :=
  x.val - M

def hwToCentered (M : ℕ) (z : ℤ) (hz : z.natAbs ≤ M) : Fin (2 * M + 1) :=
  ⟨(z + M).toNat, by
    have hzle : z ≤ (z.natAbs : ℤ) := Int.le_natAbs
    have hnzle : -z ≤ ((-z).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at hnzle
    have habs : (z.natAbs : ℤ) ≤ M := by exact_mod_cast hz
    have hlo : -(M : ℤ) ≤ z := by omega
    have hhi : z ≤ M := by omega
    have hz0 : 0 ≤ z + M := by omega
    have hz2 : z + M < 2 * M + 1 := by omega
    exact (Int.toNat_lt hz0).2 hz2⟩

def hwPairFiber (M : ℕ) (h₁ h₂ n : ℤ) :
    Finset (Fin (2 * M + 1) × Fin (2 * M + 1)) :=
  Finset.univ.filter fun x ↦
    h₁ * hwCentered M x.1 + h₂ * hwCentered M x.2 = n

noncomputable def hwSigmaInv (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (d : ℝ)⁻¹

noncomputable def hwZetaTwo : ℝ :=
  ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹

end MathlibExt.NumberTheory.HilbertWaringWanted
