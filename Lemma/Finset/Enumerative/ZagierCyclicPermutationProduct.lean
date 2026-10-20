import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.ZagierCyclicPermutationProduct
open MetaMathlibExt


/--
[zagier_probability_product_two_cyclic_permutations](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagier_probability_product_two_cyclic_permutations_eq
  {n k : ℕ}
-- given
  (hn : 0 < n)
  (hk : 0 < k)
  (hkn : k ≤ n) :
-- imply
  ((Fintype.card {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
    Multiset.card p.1.cycleType + Fintype.card (Function.fixedPoints p.1) = 1 ∧
    Multiset.card p.2.cycleType + Fintype.card (Function.fixedPoints p.2) = 1 ∧
    Multiset.card (p.1 * p.2).cycleType +
    Fintype.card (Function.fixedPoints (p.1 * p.2)) = k}) : ℚ) /
    ((Fintype.card {σ : Equiv.Perm (Fin n) //
    Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 1}) : ℚ) ^ 2 =
    (1 + (-1 : ℚ) ^ (n - k)) / Nat.factorial (n + 1) *
    Nat.stirlingFirst (n + 1) k := by
-- proof
  apply MetaMathlibExt.zagier_probability_product_two_cyclic_permutations n k hn hk hkn


-- created on 2026-10-20
