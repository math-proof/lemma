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
import Theorem.NumberTheory.HilbertWaring.Part10
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

def hwPowerSumset (k s : ℕ) : Set ℕ :=
  {n | ∃ x : Fin s → ℕ, n = ∑ i, x i ^ k}

def hwPowerFiber (k s M n : ℕ) : Finset (Fin s → Fin (M + 1)) :=
  Finset.univ.filter fun x ↦ n = ∑ i, (x i : ℕ) ^ k

def hwSplitTuple (r M : ℕ) (x : Fin (r + r) → Fin (M + 1)) :
    (Fin r → Fin (M + 1)) × (Fin r → Fin (M + 1)) :=
  (fun i ↦ x (Fin.castAdd r i), fun i ↦ x (Fin.natAdd r i))

def hwPowerCoeffs (k : ℕ) : Fin (k + 1) → ℤ :=
  fun j ↦ if j.val = k then 1 else 0

end MathlibExt.NumberTheory.HilbertWaringWanted
