import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.HighlyComposite
open Nat


/--
[IsHighlyComposite.factorization_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HighlyComposite.lean)
-/
@[path]
private lemma IsHighlyComposite_factorization_antitone_eq
  {H p q : ℕ}
-- given
  (hH : H.IsHighlyComposite)
  (hp : p.Prime)
  (hq : q.Prime)
  (hpq : p ≤ q) :
-- imply
  H.factorization q ≤ H.factorization p := by
-- proof
  apply Nat.IsHighlyComposite.factorization_antitone hH hp hq hpq

/--
[IsHighlyComposite.dvd_of_prime_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HighlyComposite.lean)
-/
@[path]
private lemma IsHighlyComposite_dvd_of_prime_le_eq
  {H p q : ℕ}
-- given
  (hH : H.IsHighlyComposite)
  (hp : p.Prime)
  (hq : q.Prime)
  (hpq : p ≤ q)
  (hqH : q ∣ H) :
-- imply
  p ∣ H := by
-- proof
  apply Nat.IsHighlyComposite.dvd_of_prime_le hH hp hq hpq hqH


-- created on 2026-10-20
