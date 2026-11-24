module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Def.Combinatorics.Schnirelmann
public import Theorem.Finset.Schnirelmann
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic
public import Theorem.NumberTheory.HilbertWaring.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/
namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

def hwPowerImage (k s M : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin s → Fin (M + 1))).image fun x ↦ ∑ i, (x i : ℕ) ^ k

end MathlibExt.NumberTheory.HilbertWaringWanted
