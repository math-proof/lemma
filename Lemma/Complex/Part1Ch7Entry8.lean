import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch7Entry8

open Ramanujan.Part1Ch7.Entry8

/--
[Part1Ch7Entry8](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry8.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry8_eq
-- given
  (r : ℕ)
  (hr : 0 < r)
  (x : ℂ) :
-- imply
  ((Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) (x + 1) -
    (Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) 1) / (r + 1 : ℂ) =
  (∑ k ∈ Finset.range (r + 1),
      ((r + 1).choose k : ℂ) * (bernoulli k : ℂ) * x ^ (r + 1 - k)) /
      (r + 1 : ℂ) + x ^ r := by
-- proof
  apply Ramanujan.Part1Ch7.Entry8.ramanujan_part1_ch7_entry8 r hr x

-- created on 2026-10-10
