/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliDuality.lean -/

-- Author: @toskua, Avocado

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

private noncomputable def Hsum (n s : ℕ) : ℚ :=
  ∑ r ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
      (((r + 1).descFactorial s : ℕ) : ℚ)

private noncomputable def Dsum (n s : ℕ) : ℚ :=
  ((s.factorial : ℕ) : ℚ) * (((s - 1).factorial : ℕ) : ℚ) * ((Nat.stirlingSecond (n + 1) s : ℕ) : ℚ) +
  (((s.factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (s + 1) : ℕ) : ℚ)

private noncomputable def Fsum (n k : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * ∑ r ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
      ((((r + 1) ^ k : ℕ)) : ℚ)

private noncomputable def Tsum (n k : ℕ) : ℚ :=
  ∑ s ∈ Finset.range (k + 1),
    ((Nat.stirlingSecond k s : ℕ) : ℚ) * Dsum n s

private noncomputable def Gsum (n k : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (k + 1),
    (((m.factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℚ) *
      ((Nat.stirlingSecond (k + 1) (m + 1) : ℕ) : ℚ)

private noncomputable def BigG (n k : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (n + k + 1),
    (((m.factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℚ) *
      ((Nat.stirlingSecond (k + 1) (m + 1) : ℕ) : ℚ)
namespace MetaMathlibExt

/-- Poly-Bernoulli number `Bₙ⁽ᵏ⁾` via Kaneko's explicit finite Stirling-number formula.

Source: Y. Hamahata and H. Masubuchi, "Special Multi-Poly-Bernoulli Numbers,"
Journal of Integer Sequences 10 (2007), Article 07.4.1,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata/hamahata3.tex>.
The poly-Bernoulli generating-series definition and Kaneko's formula are
lines 106–152 of the official TeX.

The source sums over `m = 1, …, n + 1` with denominator `(m : ℚ) ^ k`;
here this is reindexed by `r = m - 1` over `Finset.range (n + 1)`, so the
denominator is `(((r + 1 : ℕ) : ℚ) ^ k)`. The two sign factors
`(-1 : ℚ) ^ n` and `(-1 : ℚ) ^ r` are kept in this source-direct form.

Introduced by M. Kaneko, "Poly-Bernoulli numbers," Journal de Théorie des
Nombres de Bordeaux 9 (1997), 221–228; see also T. Arakawa and M. Kaneko,
"On poly-Bernoulli numbers," Commentarii Mathematici Universitatis
Sancti Pauli 48 (1999), 159–167, as cited by the source. -/
def polyBernoulli (n : ℕ) (k : ℤ) : ℚ :=
  (-1 : ℚ) ^ n * ∑ r ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) /
      (((r + 1 : ℕ) : ℚ) ^ k)
end MetaMathlibExt
