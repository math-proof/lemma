import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NetoHigherOrderBernoulli
open Finset
open MetaMathlibExt


/--
[higherOrderBernoulliNumber_nat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma higherOrderBernoulliNumber_nat_eq
  {d n : ℕ} :
-- imply
  higherOrderBernoulliNumber (d : ℂ) n =
    (n.factorial : ℂ) * PowerSeries.coeff n (bernoulliPowerSeries ℂ ^ d) := by
-- proof
  apply MetaMathlibExt.higherOrderBernoulliNumber_nat d n

/--
[higherOrderBernoulliNumber_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma higherOrderBernoulliNumber_one_eq
  {n : ℕ} :
-- imply
  higherOrderBernoulliNumber 1 n = (bernoulli n : ℂ) := by
-- proof
  apply MetaMathlibExt.higherOrderBernoulliNumber_one n

/--
[neto_higher_order_bernoulli_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_higher_order_bernoulli_identity_eq
  {x : ℂ}
  {n ℓ : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    x ^ (n - k) * (Nat.choose n k : ℂ) * higherOrderBernoulliNumber x (ℓ + k)) =
    (-1 : ℂ) ^ (n + ℓ) *
    ∑ k ∈ Finset.range (ℓ + 1),
    x ^ (ℓ - k) * (Nat.choose ℓ k : ℂ) * higherOrderBernoulliNumber x (n + k) := by
-- proof
  apply MetaMathlibExt.neto_higher_order_bernoulli_identity x n ℓ


-- created on 2026-10-20
