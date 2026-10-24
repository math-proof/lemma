/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LinnikLargeSieve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Complex

noncomputable section

namespace LinnikLargeSieve

/-- The set `P_M` of primes lying in the dyadic interval `[M/2, M]`. -/
def primesInRange (M : ℕ) : Finset ℕ :=
  (Finset.Icc (M / 2) M).filter Nat.Prime

/-- Mod-`p` projection of `f : Fin N → ℂ`: $(\pi_p f)(a) = \sum_{n \equiv a \pmod p} f(n)$. -/
def modProjection (N : ℕ) (p : ℕ) (f : Fin N → ℂ) (a : ZMod p) : ℂ :=
  ∑ n : Fin N, if ((n : ℕ) : ZMod p) = a then f n else 0

/-- Average value of `f : Fin N → ℂ`: $\bar f = \tfrac{1}{N} \sum_n f(n)$. -/
def average (N : ℕ) (f : Fin N → ℂ) : ℂ :=
  (1 / (N : ℂ)) * ∑ n : Fin N, f n

/-- High-frequency part `f_H = f - \bar f` of `f : Fin N → ℂ`. -/
def highFreqPart (N : ℕ) (f : Fin N → ℂ) : Fin N → ℂ :=
  fun n => f n - average N f

/-- Squared $L^2$ norm of `g : ZMod p → ℂ`. -/
def l2NormSq_ZMod (p : ℕ) [NeZero p] (g : ZMod p → ℂ) : ℝ :=
  ∑ a : ZMod p, ‖g a‖ ^ 2

/-- High-frequency part of `g : ZMod p → ℂ`: `g(a) - (1/p) ∑_b g(b)`. -/
def highFreqPart_ZMod (p : ℕ) [NeZero p] (g : ZMod p → ℂ) : ZMod p → ℂ :=
  fun a => g a - (1 / (p : ℂ)) * ∑ b : ZMod p, g b

/-- Squared $L^2$ norm of the high-frequency part of the mod-`p` projection:
`‖(π_p f)_H‖_{L^2}^2`. -/
def projHighFreqL2Sq (N : ℕ) (p : ℕ) [NeZero p] (f : Fin N → ℂ) : ℝ :=
  l2NormSq_ZMod p (highFreqPart_ZMod p (modProjection N p f))

/-- Left-hand side of Linnik's large sieve inequality:
$\sum_{p \in P_M} \|(\pi_p f)_H\|_{L^2}^2$. -/
def linnikLHS (N M : ℕ) (f : Fin N → ℂ) : ℝ :=
  ∑ p ∈ primesInRange M,
    if hp : p = 0 then 0
    else haveI : NeZero p := ⟨hp⟩; projHighFreqL2Sq N p f

/-- Fourier transform on $\mathbb{Z}$: $\hat f(\xi) = \sum_n f(n) e^{-2\pi i \xi n}$. -/
def fourierZ (N : ℕ) (f : Fin N → ℂ) (ξ : ℝ) : ℂ :=
  ∑ n : Fin N, f n * Complex.exp (-2 * ↑Real.pi * Complex.I * ↑ξ * ↑(n : ℕ))

/-- Bombieri–Davenport form of the analytic large sieve: for any `1/N`-separated set
`S ⊆ [0, 1)`, $\sum_{\xi \in S} |\hat f(\xi)|^2 \le (2N - 1) \sum_n |f(n)|^2$. -/
def fareySet (M : ℕ) : Finset ℝ :=
  (primesInRange M).biUnion fun p =>
    (Finset.Icc 1 (p - 1)).image fun (α : ℕ) => (α : ℝ) / (p : ℝ)
