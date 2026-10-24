/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianGenocchiDivisibility.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import sympy.atlas.Combinatorics.Enumerative.MedianGenocchiNumber
import Lemma.Finset.Enumerative.MedianGenocchiNumber
import Lemma.Finset.Enumerative.EulerSeidelMatrix
import sympy.atlas.Combinatorics.Enumerative.EulerSeidelMatrix
import Lemma.Nat.GenocchiBernoulli
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Ring

open scoped BigOperators

/-!
# Divisibility of median Genocchi numbers

This file proves Chen's power-of-two divisibility and modulo-six congruence for
the odd-indexed median Genocchi numbers. It connects their Bernoulli definition
to a finite Euler-Seidel and Legendre-Stirling table, then normalizes that table
over the integers.
-/

namespace MetaMathlibExt

private def mgenTransform (a : ℕ → ℚ) (c : ℚ) (m : ℕ) : ℚ :=
  a (m + 2) + a (m + 1) - c * a m

private def mgenBasisSeq : ℕ → ℕ → ℚ
  | 0 => genocchiNumberViaBernoulli
  | k + 1 => mgenTransform (mgenBasisSeq k) ((k : ℚ) * (k + 1))

private def mgenLS : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => mgenLS n k + (k + 1) * (k + 2) * mgenLS n (k + 1)

private def mgenLIter : ℕ → ℕ → ℚ
  | 0 => genocchiNumberViaBernoulli
  | n + 1 => mgenTransform (mgenLIter n) 0

private def mgenNormalizedLS : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      mgenNormalizedLS n k + ((k + 1) * (k + 2) / 2) * mgenNormalizedLS n (k + 1)

private def mgenFactor : ℕ → ℕ
  | 0 => 1
  | k + 1 => mgenFactor k * ((k + 1) * (k + 2) / 2)

private def mgenQuotient (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (n + k) * (mgenNormalizedLS n k : ℤ) * (mgenFactor k : ℤ)
end MetaMathlibExt
