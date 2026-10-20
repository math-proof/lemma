import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MotzkinCentralTrinomial
open scoped BigOperators
open MetaMathlibExt


/--
[trinomialCoefficient_self_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinCentralTrinomial.lean)
-/
@[path]
private lemma trinomialCoefficient_self_eq_sum_eq
  {n : ℕ} :
-- imply
  trinomialCoefficient n n =
    ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * (2 * k).choose k := by
-- proof
  apply MetaMathlibExt.trinomialCoefficient_self_eq_sum n

/--
[motzkin_central_trinomial_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinCentralTrinomial.lean)
-/
@[path]
private lemma motzkin_central_trinomial_recurrence_eq
  {M : ℕ → ℕ}
-- given
  (hM : ∀ n, M n = ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * catalan k) :
-- imply
  ∀ n, 1 ≤ n →
    trinomialCoefficient (n + 1) (n + 1) =
    trinomialCoefficient n n + 2 * n * M (n - 1) := by
-- proof
  apply MetaMathlibExt.motzkin_central_trinomial_recurrence M hM


-- created on 2026-10-20
