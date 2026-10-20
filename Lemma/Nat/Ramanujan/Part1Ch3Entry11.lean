import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry11
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry11


/--
[ramanujan_part1_ch3_entry11](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry11.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry11_eq
  {A p : ℕ → ℝ}
  {R : ℝ}
  {f : ℝ → ℝ}
-- given
  (hR : 0 < R)
  (hf : ∀ x : ℝ, |x| < R → HasSum (fun n : ℕ => A (n + 1) * x ^ (n + 1) / (↑(n + 1) : ℝ)) (f x))
  (hg : ∀ x : ℝ, |x| < R → HasSum (fun n : ℕ => p n * x ^ n) (Real.exp (f x))) :
-- imply
  ∀ n : ℕ, 0 < n → (↑n : ℝ) * p n = ∑ k ∈ Finset.Icc 1 n, A k * p (n - k) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry11.ramanujan_part1_ch3_entry11 A p R f hR hf hg


-- created on 2026-10-20
