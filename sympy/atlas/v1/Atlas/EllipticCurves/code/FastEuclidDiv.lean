/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FastEuclidDiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace IntegerLongDivision

/-- One step of binary long division by `b`: given the current quotient/remainder pair `qr` and the
next bit `bit` of the dividend, shift the partial quotient/remainder left by one (i.e., multiply by
`2`), add `bit` to the remainder, and conditionally subtract `b` to keep the remainder smaller
than `b`. -/
def longDivStep (b : ℕ) (bit : Bool) (qr : ℕ × ℕ) : ℕ × ℕ :=
  let q' := 2 * qr.1
  let r' := 2 * qr.2 + bit.toNat
  if r' < b then (q', r') else (q' + 1, r' - b)

/-- Recursive driver of binary long division: starting from the most significant bit `m` of `a`,
folds `longDivStep` over `k+1` iterations consuming successive bits from `m` down to `m - k - 1`.
The result is the quotient/remainder pair after processing those bits. -/
def longDivLoop (a b m : ℕ) : ℕ → ℕ × ℕ
  | 0     => longDivStep b (a.testBit m) (0, 0)
  | k + 1 => longDivStep b (a.testBit (m - k - 1)) (longDivLoop a b m k)

/-- Schoolbook binary long division of `a` by `b`, treating `a` as an `(m+1)`-bit number: returns
the quotient/remainder pair after processing all bits from position `m` down to `0`. -/
def longDiv (a b m : ℕ) : ℕ × ℕ := longDivLoop a b m m

/-- Natural-number long division specialized to the bit-length of `a`: uses `Nat.log 2 a` as the
top bit index, yielding a quotient/remainder pair for `a / b`. -/
def longDivNat (a b : ℕ) : ℕ × ℕ :=
  longDiv a b (Nat.log 2 a)

end IntegerLongDivision
