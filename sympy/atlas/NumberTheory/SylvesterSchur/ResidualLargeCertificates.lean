/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ResidualLargeCertificates.lean -/

/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.PrimeCounting

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring
import Lemma.Nat.SylvesterSchur.ResidualFinite
/-!
# Finite certificates for the large residual Sylvester-Schur estimates

This file contains the explicit prime-counting and endpoint power certificates used for the
mid residual range in `MathlibExt.NumberTheory.SylvesterSchur.ResidualLarge`.

## Main statements

* `second_residual_mid_primeCounting_lt_start_pow`: the finite prime-counting estimate for
  `38 ≤ n < 945` and `1291 ≤ k`.

## Implementation notes

The prime-counting certificates avoid one large computation by sieving with the primes up to
`29`, covering the remaining candidate set by private interval chunks, and exposing only the
resulting prime-counting bounds.  The endpoint power certificates are similarly hidden behind
mathematical inequalities for the relevant segments.  The numerical constants in this file are
certificate data for those interval and endpoint checks, not downstream API.
-/

namespace Nat.SylvesterSchur
namespace Internal

open Finset Nat

private def smallSievePrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}

private def smallSieveProduct : ℕ := 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29

private def factorialSieveCandidates (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun m => m ≠ 1 ∧ Nat.Coprime smallSieveProduct m)

private def sieveChunk (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter (fun m => m ≠ 1 ∧ Nat.Coprime smallSieveProduct m)

private def finsetUnionList : List (Finset ℕ) → Finset ℕ
  | [] => ∅
  | s :: ss => s ∪ finsetUnionList ss

private def finsetCardSum : List (Finset ℕ) → ℕ
  | [] => 0
  | s :: ss => s.card + finsetCardSum ss

private def sieveChunksOfBounds (bounds : List (ℕ × ℕ)) : List (Finset ℕ) :=
  bounds.map fun b => sieveChunk b.1 b.2

private def sieveBounds509 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 509)]

private def sieveChunks509 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds509

private def sieveBounds715 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 599),
    (600, 699), (700, 715)]

private def sieveChunks715 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds715

private def sieveBounds855 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 599),
    (600, 699), (700, 799), (800, 855)]

private def sieveChunks855 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds855

private def sieveBounds917 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 599),
    (600, 699), (700, 799), (800, 899), (900, 917)]

private def sieveChunks917 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds917

private def sieveBounds940 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 599),
    (600, 699), (700, 799), (800, 899), (900, 940)]

private def sieveChunks940 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds940

private def sieveBounds944 : List (ℕ × ℕ) :=
  [(0, 99), (100, 199), (200, 299), (300, 399), (400, 499), (500, 599),
    (600, 699), (700, 799), (800, 899), (900, 944)]

private def sieveChunks944 : List (Finset ℕ) :=
  sieveChunksOfBounds sieveBounds944

/-! ### Power endpoint certificates -/

/- A small binary-power certificate keeps the following endpoint checks from relying on a
raised exponentiation evaluator threshold. -/
private def pow1291_1 : ℕ := 1291
private def pow1291_2 : ℕ := pow1291_1 * pow1291_1
private def pow1291_4 : ℕ := pow1291_2 * pow1291_2
private def pow1291_8 : ℕ := pow1291_4 * pow1291_4
private def pow1291_16 : ℕ := pow1291_8 * pow1291_8
private def pow1291_32 : ℕ := pow1291_16 * pow1291_16
private def pow1291_64 : ℕ := pow1291_32 * pow1291_32
private def pow1291_128 : ℕ := pow1291_64 * pow1291_64
private def pow1291_256 : ℕ := pow1291_128 * pow1291_128
private def pow1291_512 : ℕ := pow1291_256 * pow1291_256
end Internal
end Nat.SylvesterSchur
