import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.BinomialTransformSecondOrderHarmonic
open MetaMathlibExt


/--
[binomial_transform_second_order_harmonic_numbers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialTransformSecondOrderHarmonic.lean)
-/
@[path]
private lemma binomial_transform_second_order_harmonic_numbers_eq
  {s : ℂ}
  {n : ℕ}
-- given
  (hn : 0 < n)
  (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) :
-- imply
  (∑ k ∈ Finset.Icc 1 n,
    (-1 : ℂ) ^ k *
    ((Finset.range k).prod (fun j => s + (n : ℂ) - (j : ℂ)) /
    (Nat.factorial k : ℂ)) *
    (∑ j ∈ Finset.Icc 1 k, (1 : ℂ) / (j : ℂ) ^ 2)) =
    (-1 : ℂ) ^ n *
    ((Finset.range n).prod (fun j => s + (n : ℂ) - 1 - (j : ℂ)) /
    (Nat.factorial n : ℂ)) *
    (∑ j ∈ Finset.Icc 1 n, (1 : ℂ) / (j : ℂ) ^ 2) -
    1 / (s + (n : ℂ)) *
    ((∑ j ∈ Finset.Icc 1 n, (1 : ℂ) / (j : ℂ)) -
    s * ∑ k ∈ Finset.Icc 1 n,
    ((-1 : ℂ) ^ k *
    ((Finset.range (k - 1)).prod
    (fun j => s + (k : ℂ) - 1 - (j : ℂ)) /
    (Nat.factorial (k - 1) : ℂ))) /
    ((k : ℂ) ^ 2 * (n.choose k : ℂ))) := by
-- proof
  apply MetaMathlibExt.binomial_transform_second_order_harmonic_numbers s n hn hs


-- created on 2026-10-20
