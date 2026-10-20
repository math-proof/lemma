import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.LcmProductIdentity
open MetaMathlibExt


/--
[lcm_product_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/LcmProductIdentity.lean)
-/
@[path]
private lemma lcm_product_identity_eq
  {n : ℕ} :
-- imply
  ∏ p ∈ Nat.primesBelow (n + 2), p ^ (n / (p - 1)) =
    Finset.lcm (Finset.image (fun t : Fin n → Fin (2 * n + 1) => ∏ j, (t j).val)
    (Finset.univ.filter
    (fun t => (∀ j, 1 ≤ (t j).val) ∧ ∑ j, (t j).val ≤ 2 * n))) id := by
-- proof
  apply MetaMathlibExt.lcm_product_identity n


-- created on 2026-10-20
