import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedCatalanPrimeDivisibility
open MetaMathlibExt


/--
[generalizedCatalan_prime_dvd_iff_not_geometric_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedCatalanPrimeDivisibility.lean)
-/
@[path]
private lemma generalizedCatalan_prime_dvd_iff_not_geometric_sum_eq
  {p n : ℕ}
-- given
  (hp : p.Prime) :
-- imply
  p ∣ Nat.choose (p * n) n / ((p - 1) * n + 1) ↔
    ∀ k : ℕ, n ≠ (p ^ k - 1) / (p - 1) := by
-- proof
  apply MetaMathlibExt.generalizedCatalan_prime_dvd_iff_not_geometric_sum p n hp


-- created on 2026-10-20
