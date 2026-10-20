import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.GeneralizedFibonacciIdentities
open MetaMathlibExt


/--
[generalizedFibonacci_binet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedFibonacciIdentities.lean)
-/
@[path]
private lemma generalizedFibonacci_binet_eq
  {p : ℝ}
  {W : ℕ → ℝ}
  {n : ℕ}
-- given
  (hW : ∀ k, W (k + 2) = p * W (k + 1) + W k) :
-- imply
  W n = (W 1 - W 0 * ((p - Real.sqrt (p ^ 2 + 4)) / 2)) / Real.sqrt (p ^ 2 + 4) *
    ((p + Real.sqrt (p ^ 2 + 4)) / 2) ^ n +
    (W 0 * ((p + Real.sqrt (p ^ 2 + 4)) / 2) - W 1) / Real.sqrt (p ^ 2 + 4) *
    ((p - Real.sqrt (p ^ 2 + 4)) / 2) ^ n := by
-- proof
  apply MetaMathlibExt.generalizedFibonacci_binet p W hW n

/--
[generalizedFibonacci_mixed_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedFibonacciIdentities.lean)
-/
@[path]
private lemma generalizedFibonacci_mixed_identity_eq
  {p : ℝ}
  {W F : ℤ → ℝ}
  {m n : ℤ}
-- given
  (hWrec : ∀ k : ℤ, W (k + 2) = p * W (k + 1) + W k)
  (hF0 : F 0 = 0)
  (hF1 : F 1 = 1)
  (hFrec : ∀ k : ℤ, F (k + 2) = p * F (k + 1) + F k) :
-- imply
  F (m - 2) * W (n - 2) - F (m - 3) * W (n - 1) = (-1 : ℝ) ^ (m - 1) * W (n - m + 1) := by
-- proof
  apply MetaMathlibExt.generalizedFibonacci_mixed_identity p W F hWrec hF0 hF1 hFrec m n

/--
[generalizedFibonacci_cassini](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedFibonacciIdentities.lean)
-/
@[path]
private lemma generalizedFibonacci_cassini_eq
  [CommRing R]
  {p : R}
  {W : ℕ → R}
  {n : ℕ}
-- given
  (hW : ∀ k, W (k + 2) = p * W (k + 1) + W k) :
-- imply
  W n * W (n + 2) - W (n + 1) ^ 2 = (-1) ^ n * (W 0 ^ 2 + p * W 0 * W 1 - W 1 ^ 2) := by
-- proof
  apply MetaMathlibExt.generalizedFibonacci_cassini p W hW n

/--
[generalizedFibonacci_tendsto_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedFibonacciIdentities.lean)
-/
@[path]
private lemma generalizedFibonacci_tendsto_ratio_eq
  {p : ℝ}
  {W : ℕ → ℝ}
-- given
  (hp : 0 < p)
  (hW0 : 0 ≤ W 0)
  (hW1 : 0 < W 1)
  (hW : ∀ k, W (k + 2) = p * W (k + 1) + W k) :
-- imply
  Filter.Tendsto (fun k => W (k + 1) / W k) Filter.atTop
    (nhds ((p + Real.sqrt (p ^ 2 + 4)) / 2)) := by
-- proof
  apply MetaMathlibExt.generalizedFibonacci_tendsto_ratio p hp W hW0 hW1 hW

/--
[generalizedFibonacci_binet_cassini_and_ratio_limit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedFibonacciIdentities.lean)
-/
@[path]
private lemma generalizedFibonacci_binet_cassini_and_ratio_limit_eq
  {p a b : ℤ}
  {W F : ℤ → ℝ}
  {m n : ℤ}
-- given
  (hp : 1 ≤ p)
  (ha : 0 ≤ a)
  (hb : 0 < b)
  (hm : 0 ≤ m)
  (hn : 0 ≤ n)
  (hW0 : W 0 = (a : ℝ))
  (hW1 : W 1 = (b : ℝ))
  (hWrec : ∀ k : ℤ, W (k + 2) = (p : ℝ) * W (k + 1) + W k)
  (hF0 : F 0 = 0)
  (hF1 : F 1 = 1)
  (hFrec : ∀ k : ℤ, F (k + 2) = (p : ℝ) * F (k + 1) + F k) :
-- imply
  (W n =
    ((((b : ℝ) - (a : ℝ) * (((p : ℝ) - Real.sqrt ((p : ℝ) ^ 2 + 4)) / 2)) / Real.sqrt
    ((p : ℝ) ^ 2 + 4)) * ((((p : ℝ) + Real.sqrt ((p : ℝ) ^ 2 + 4)) / 2) ^ n) +
    (((a : ℝ) * (((p : ℝ) + Real.sqrt ((p : ℝ) ^ 2 + 4)) / 2) - (b : ℝ)) / Real.sqrt
    ((p : ℝ) ^ 2 + 4)) * ((((p : ℝ) - Real.sqrt ((p : ℝ) ^ 2 + 4)) / 2) ^ n)) ∧ F (m - 2) * W
    (n - 2) - F (m - 3) * W (n - 1) = (-1 : ℝ) ^ (m - 1) * W (n - m + 1) ∧ W n * W (n + 2) - W
    (n + 1) ^ 2 = (-1 : ℝ) ^ n * ((a : ℝ) ^ 2 + (p : ℝ) * (a : ℝ) * (b : ℝ) - (b : ℝ) ^ 2) ∧
    Filter.Tendsto (fun k : ℕ => W (↑k + 1) / W ↑k) Filter.atTop
    (nhds ((((p : ℝ) + Real.sqrt ((p : ℝ) ^ 2 + 4)) / 2)))) := by
-- proof
  apply MetaMathlibExt.generalizedFibonacci_binet_cassini_and_ratio_limit p a b W F m n hp ha hb hm hn hW0 hW1 hWrec hF0 hF1 hFrec


-- created on 2026-10-20
