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
import Theorem.NumberTheory.HilbertWaring.Part4
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

def hwTupleSum (r N : ℕ) (f : ℕ → ℤ) (x : Fin r → Fin (N + 1)) : ℤ :=
  ∑ i, f (x i)

noncomputable def hwWeylSum (P N : ℕ) [NeZero P]
    (f : ℕ → ℤ) (a : ZMod P) : ℂ :=
  ∑ n : Fin (N + 1), ZMod.stdAddChar (a * (f n : ZMod P))

def hwMomentFinset (r N : ℕ) (f : ℕ → ℤ) :
    Finset ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  Finset.univ.filter fun xy ↦ hwTupleSum r N f xy.1 = hwTupleSum r N f xy.2

def hwFinLift {A B : ℕ} (hAB : A ≤ B) (x : Fin (A + 1)) : Fin (B + 1) :=
  ⟨x.val, by omega⟩

def hwMomentLift (r A B : ℕ) (hAB : A ≤ B) :
    ((Fin r → Fin (A + 1)) × (Fin r → Fin (A + 1))) →
      ((Fin r → Fin (B + 1)) × (Fin r → Fin (B + 1))) :=
  fun p ↦ (fun i ↦ hwFinLift hAB (p.1 i), fun i ↦ hwFinLift hAB (p.2 i))

def hwTupleImage (r N : ℕ) (f : ℕ → ℤ) : Finset ℤ :=
  (Finset.univ : Finset (Fin r → Fin (N + 1))).image (hwTupleSum r N f)

def hwValueFiber (r N : ℕ) (f : ℕ → ℤ) (t : ℤ) :
    Finset (Fin r → Fin (N + 1)) :=
  Finset.univ.filter fun x ↦ hwTupleSum r N f x = t

def hwDiffFiber (r N : ℕ) (f : ℕ → ℤ) (m : ℤ) :
    Finset ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  Finset.univ.filter fun p ↦ hwTupleSum r N f p.1 - hwTupleSum r N f p.2 = m

def hwSumFiber (r N : ℕ) (f : ℕ → ℤ) (m : ℤ) :
    Finset ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  Finset.univ.filter fun p ↦ hwTupleSum r N f p.1 + hwTupleSum r N f p.2 = m

def hwPolyEval (k : ℕ) (a : Fin (k + 1) → ℤ) (n : ℕ) : ℤ :=
  ∑ j, a j * (n : ℤ) ^ j.val

def hwCoeffBound (k c N : ℕ) (a : Fin (k + 1) → ℤ) : Prop :=
  ∀ j, (a j).natAbs ≤ c * N ^ (k - j.val)

end MathlibExt.NumberTheory.HilbertWaringWanted
