import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.AbelHurwitzBernoulli
open scoped BigOperators
open MetaMathlibExt


/--
[abel_hurwitz_bernoulli_multinomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/AbelHurwitzBernoulli.lean)
-/
@[path]
private lemma abel_hurwitz_bernoulli_multinomial_eq
  {m n : ℕ}
  {x : Fin m → ℚ}
  {r : Fin m}
-- given
  (hm : 2 ≤ m) :
-- imply
  ∑ l ∈ (Fintype.piFinset (fun _ : Fin m => Finset.range (n + 1))).filter
    (fun l => ∑ i, l i = n),
    (Nat.multinomial Finset.univ l : ℚ) *
    (Polynomial.eval (x r + (l r : ℚ)) (Polynomial.bernoulli (l r)) *
    ∏ j ∈ Finset.univ.erase r, (x j + (l j : ℚ)) ^ l j) =
    ∑ l ∈ Finset.range (n + 1),
    (Nat.choose n l : ℚ) *
    ((Nat.factorial (m + l - 2) : ℚ) / (Nat.factorial (m - 2) : ℚ)) *
    Polynomial.eval ((∑ i, x i) + (n : ℚ)) (Polynomial.bernoulli (n - l)) := by
-- proof
  apply MetaMathlibExt.abel_hurwitz_bernoulli_multinomial m n x r hm


-- created on 2026-10-20
