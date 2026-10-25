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
import Abbrev.NumberTheory.HilbertWaring.Part3
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

def hwPairSignedDiff (N : ℕ) (p : hwOffDiag N) : hwSigned N :=
  if hp : p.1.2 < p.1.1 then
    (0, ⟨p.1.1.val - p.1.2.val - 1, by
      have hx := p.1.1.isLt
      have hpv : p.1.2.val < p.1.1.val := hp
      omega⟩)
  else
    (1, ⟨p.1.2.val - p.1.1.val - 1, by
      have hy := p.1.2.isLt
      have hne := p.2
      omega⟩)

def hwPairBase (N : ℕ) (p : hwOffDiag N) : Fin (N + 1) :=
  if p.1.2 < p.1.1 then p.1.2 else p.1.1

def hwOffDiagFiber (N : ℕ) (h : hwSigned N) : Finset (hwOffDiag N) :=
  Finset.univ.filter fun p ↦ hwPairSignedDiff N p = h

noncomputable def hwDiffBlock (P N : ℕ) [NeZero P] (f : ℕ → ℤ)
    (h : hwSigned N) (a : ZMod P) : ℂ :=
  ∑ p ∈ hwOffDiagFiber N h,
    ZMod.stdAddChar (a * ((f p.1.1 - f p.1.2 : ℤ) : ZMod P))

def hwBlockLength (N : ℕ) (h : hwSigned N) : ℕ :=
  N - (h.2.val + 1)

def hwPairOfBase (N : ℕ) (h : hwSigned N)
    (y : Fin (hwBlockLength N h + 1)) : hwOffDiag N :=
  if hs : h.1 = 0 then
    ⟨(⟨y.val + h.2.val + 1, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩, ⟨y.val, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩), by
      intro heq
      have heqval : y.val + h.2.val + 1 = y.val :=
        congrArg (fun z : Fin (N + 1) ↦ z.val) heq
      omega⟩
  else
    ⟨(⟨y.val, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩, ⟨y.val + h.2.val + 1, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩), by
      intro heq
      have heqval : y.val = y.val + h.2.val + 1 :=
        congrArg (fun z : Fin (N + 1) ↦ z.val) heq
      omega⟩

end MathlibExt.NumberTheory.HilbertWaringWanted
