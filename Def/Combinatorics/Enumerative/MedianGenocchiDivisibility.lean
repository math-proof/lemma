/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianGenocchiDivisibility.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Def.Combinatorics.Enumerative.MedianGenocchiNumber
public import Theorem.Finset.Enumerative.MedianGenocchiNumber
public import Theorem.Finset.Enumerative.EulerSeidelMatrix
public import Def.Combinatorics.Enumerative.EulerSeidelMatrix
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

/-!
# Divisibility of median Genocchi numbers

This file proves Chen's power-of-two divisibility and modulo-six congruence for
the odd-indexed median Genocchi numbers. It connects their Bernoulli definition
to a finite Euler-Seidel and Legendre-Stirling table, then normalizes that table
over the integers.
-/


namespace MetaMathlibExt

def mgenTransform (a : ℕ → ℚ) (c : ℚ) (m : ℕ) : ℚ :=
  a (m + 2) + a (m + 1) - c * a m

def mgenBasisSeq : ℕ → ℕ → ℚ
  | 0 => genocchiNumberViaBernoulli
  | k + 1 => mgenTransform (mgenBasisSeq k) ((k : ℚ) * (k + 1))

def mgenLS : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => mgenLS n k + (k + 1) * (k + 2) * mgenLS n (k + 1)

def mgenLIter : ℕ → ℕ → ℚ
  | 0 => genocchiNumberViaBernoulli
  | n + 1 => mgenTransform (mgenLIter n) 0

def mgenNormalizedLS : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      mgenNormalizedLS n k + ((k + 1) * (k + 2) / 2) * mgenNormalizedLS n (k + 1)

def mgenFactor : ℕ → ℕ
  | 0 => 1
  | k + 1 => mgenFactor k * ((k + 1) * (k + 2) / 2)

def mgenQuotient (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (n + k) * (mgenNormalizedLS n k : ℤ) * (mgenFactor k : ℤ)

end MetaMathlibExt
