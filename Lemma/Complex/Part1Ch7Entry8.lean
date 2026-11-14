import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch7Entry8

open Ramanujan.Part1Ch7.Entry8
open scoped Nat Real BigOperators Interval Polynomial
open Filter Finset Complex Topology


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8

/--
[eval₂_bernoulli_shift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry8.lean)
-/
@[path]
private lemma eval₂_bernoulli_shift_eq (n : ℕ) (x : ℂ) :
  (Polynomial.bernoulli n).eval₂ (algebraMap ℚ ℂ) (x + 1) =
    (Polynomial.bernoulli n).eval₂ (algebraMap ℚ ℂ) x + (n : ℂ) * x ^ (n - 1) :=
  eval₂_bernoulli_shift n x

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8

/--
[eval₂_bernoulli_expand](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry8.lean)
-/
@[path]
private lemma eval₂_bernoulli_expand_eq (n : ℕ) (x : ℂ) :
  (Polynomial.bernoulli n).eval₂ (algebraMap ℚ ℂ) x =
    ∑ k ∈ Finset.range (n + 1),
      ((n.choose k : ℕ) : ℂ) * ((bernoulli k : ℚ) : ℂ) * x ^ (n - k) :=
  eval₂_bernoulli_expand n x

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8

/--
[eval₂_bernoulli_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry8.lean)
-/
@[path]
private lemma eval₂_bernoulli_one_eq (n : ℕ) (hn : n ≠ 1) :
  (Polynomial.bernoulli n).eval₂ (algebraMap ℚ ℂ) 1 = ((bernoulli n : ℚ) : ℂ) :=
  eval₂_bernoulli_one n hn

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8

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
      (r + 1 : ℂ) + x ^ r :=
-- proof
  ramanujan_part1_ch7_entry8 r hr x

end MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8


-- created on 2026-10-10
-- updated on 2026-10-26
