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
public import Abbrev.NumberTheory.HilbertWaring.Part4


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

def hwBlockChoiceDiff (k r N : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) (z : hwBlockChoice r N) : ℤ :=
  hwTupleSum r (hwBlockLength N z.1)
      (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (z.1.2.val + 1))) z.2.1 -
    hwTupleSum r (hwBlockLength N z.1)
      (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (z.1.2.val + 1))) z.2.2

def hwBlockChoiceFreq (k r N : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) (z : hwBlockChoice r N) : ℤ :=
  hwSignedVal N z.1 * hwBlockChoiceDiff k r N hk a z

def hwZeroQuadruples {C : Type*} [Fintype C] (v : C → ℤ) :
    Finset (Fin 4 → C) :=
  Finset.univ.filter fun u ↦ ∑ i, v (u i) = 0

def hwBlockQuadMap (k r N M : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    (u : Fin 4 → hwBlockChoice r N) :
    (Fin 4 → Fin (2 * N + 1)) × (Fin 4 → Fin (2 * M + 1)) :=
  (fun i ↦ hwSignedToCentered N (u i).1,
    fun i ↦ hwToCentered M (hwBlockChoiceDiff k r N hk a (u i)) (hm (u i)))

end MathlibExt.NumberTheory.HilbertWaringWanted
