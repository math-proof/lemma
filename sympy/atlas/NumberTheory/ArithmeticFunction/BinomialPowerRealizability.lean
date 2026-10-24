/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/BinomialPowerRealizability.lean -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import sympy.atlas.NumberTheory.DoldSequence
namespace MetaMathlibExt

section

/-- Realizability of binomial-power sequences (Apéry, Delannoy, Franel).

`binomialPowerSeq r s n = ∑_k C(n,k)^r C(n+k,k)^s` over `k ≤ n`, whose
specializations include the Apéry numbers (`r = s = 2`), central Delannoy
numbers (`r = s = 1`), and Franel numbers of order `r` (`s = 0`).
`doldRealizable` is the Möbius criterion: `(μ*a)(n)` is non-negative and
divisible by `n` for all `n ≥ 1`. The wanted theorem is realizability for
every `s ≥ 0` and `r ≥ 1`.

Source: Geng-Rui Zhang, "Realizability of Some Combinatorial Sequences,"
Journal of Integer Sequences 27 (2024), Article 24.3.3, Theorem
(label Thm1.13), lines 143–144,
https://cs.uwaterloo.ca/journals/JIS/VOL27/Zhang/zhang9.tex
with `A(n,r,s)` at lines 120–122 (label Def1.5) and realizability at
lines 86–93 (label Def1.1). -/
def binomialPowerSeq (r s n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k) ^ r * (Nat.choose (n + k) k) ^ s

/-- Möbius criterion for Dold realizability: the Dold congruences
(`n ∣ (μ * a) n`) plus non-negativity of the Möbius transform.

The divisibility half is the classical Dold condition; the repository's
trace-side characterization is `MetaMathlibExt.IsDoldSequence`
(Wójcik, Lemma 3). The equivalence between the two forms is not
formalized here. -/
def doldRealizable (a : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 0 < n →
    (n : ℤ) ∣ ∑ d ∈ Nat.divisors n,
      (⇑ArithmeticFunction.moebius d) * a (n / d) ∧
    0 ≤ ∑ d ∈ Nat.divisors n,
      (⇑ArithmeticFunction.moebius d) * a (n / d)
end
end MetaMathlibExt
