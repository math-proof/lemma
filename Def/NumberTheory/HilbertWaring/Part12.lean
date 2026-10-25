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
import Theorem.NumberTheory.HilbertWaring.Part8
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

def hwStepR (k : ℕ) : ℕ := 4 * 8 ^ (k - 3)

def hwStepD (k c : ℕ) : ℕ := (k + 1) * c * 2 ^ k

def hwStepV (k c N : ℕ) : ℕ :=
  k * hwStepD k c * N ^ (k - 1)

def hwStepM (k c N : ℕ) : ℕ :=
  max N (2 * hwStepR k * hwStepV k c N)

def hwStepE (k c : ℕ) : ℕ :=
  2 * hwStepR k * k * hwStepD k c + 1

end MathlibExt.NumberTheory.HilbertWaringWanted
