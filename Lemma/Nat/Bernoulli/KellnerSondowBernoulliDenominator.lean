import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.KellnerSondowBernoulliDenominator
open MetaMathlibExt


/--
[kellner_sondow_bernoulli_denom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/KellnerSondowBernoulliDenominator.lean)
-/
@[path]
private lemma kellner_sondow_bernoulli_denom_eq
  :
-- imply
  ∀ (n : ℕ), 1 ≤ n →
    (Polynomial.bernoulli n).support.lcm (fun i => ((Polynomial.bernoulli n).coeff i).den) =
    Finset.prod
    ((Finset.range (n + 2)).filter
    (fun p => Nat.Prime p ∧ ¬ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum))
    (fun p => p) *
    Finset.prod
    ((Finset.range (n + 2)).filter
    (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum))
    (fun p => p) *
    Finset.prod
    ((Finset.range (n + 2)).filter
    (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ (Nat.digits p (n + 1)).sum < p))
    (fun p => p) := by
-- proof
  apply MetaMathlibExt.kellner_sondow_bernoulli_denom


-- created on 2026-10-20
