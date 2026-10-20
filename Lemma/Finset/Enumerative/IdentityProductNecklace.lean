import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.IdentityProductNecklace
open MetaMathlibExt


/--
[identity_product_necklace_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean)
-/
@[path]
private lemma identity_product_necklace_count_eq
  [Group G] [Fintype G] [DecidableEq G]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (Set.ncard
    { O : Set (Fin n → G) | ∃ x : Fin n → G, (List.ofFn x).prod = 1 ∧ O =
    { y | ∃ m : ℕ, m < n ∧ ∀ i : Fin n, y i = x ⟨(i.val + m) % n, Nat.mod_lt _ hn⟩ } } : ℚ) =
    (1 / (n : ℚ)) * Finset.sum (Nat.divisors n)
    (fun d => (Nat.totient (n / d) : ℚ) * (Fintype.card { g : G // g ^ (n / d) = 1 } : ℚ) *
    ((Fintype.card G : ℚ) ^ (d - 1))) := by
-- proof
  apply MetaMathlibExt.identity_product_necklace_count G n hn


-- created on 2026-10-20
