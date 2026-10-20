import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.TaxicabSeed
open MetaMathlibExt


/--
[generalized_taxicab_seed_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TaxicabSeed.lean)
-/
@[path]
private lemma generalized_taxicab_seed_exists_eq
  {m t : ℕ}
  {T : ℕ → ℕ → ℕ → Option ℕ}
-- given
  (hm : 1 ≤ m)
  (ht : 1 ≤ t)
  (hT : ∀ n v : ℕ, T n m t = some v ↔ (t ≤ Set.ncard {M : Multiset ℕ | M.card = n ∧ (∀ x ∈ M, 0 < x) ∧ (M.map (fun x => x ^ m)).sum = v} ∧ ∀ v' : ℕ, v' < v → ¬ (t ≤ Set.ncard {M : Multiset ℕ | M.card = n ∧ (∀ x ∈ M, 0 < x) ∧ (M.map (fun x => x ^ m)).sum = v'}))) :
-- imply
  ∃ s₀ : ℕ, 0 < s₀ ∧
    (∃ v₀ : ℕ, T s₀ m t = some v₀ ∧ ∀ k : ℕ, T (s₀ + k) m t = some (v₀ + k)) ∧
    ∀ s : ℕ, 0 < s →
    (∃ v : ℕ, T s m t = some v ∧ ∀ k : ℕ, T (s + k) m t = some (v + k)) →
    s₀ ≤ s := by
-- proof
  apply MetaMathlibExt.generalized_taxicab_seed_exists m t hm ht T hT


-- created on 2026-10-20
