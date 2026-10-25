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
import Theorem.NumberTheory.HilbertWaring.Part6
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

def hwDiffCoeff (k : ℕ) (a : Fin (k + 1) → ℤ) (h : ℕ) : Fin k → ℤ :=
  fun i ↦ ∑ j : Fin (k + 1), if i.val < j.val then
    a j * (j.val.choose i.val : ℤ) * (h : ℤ) ^ (j.val - i.val - 1) else 0

def hwDiffCoeffs (k : ℕ) (hk : 0 < k) (a : Fin (k + 1) → ℤ) (h : ℕ) :
    Fin (k - 1 + 1) → ℤ :=
  fun i ↦ hwDiffCoeff k a h ⟨i.val, by omega⟩

end MathlibExt.NumberTheory.HilbertWaringWanted
