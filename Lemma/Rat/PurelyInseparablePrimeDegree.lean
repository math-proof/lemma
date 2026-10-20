import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.PurelyInseparablePrimeDegree
open IntermediateField Module Polynomial
open IsPurelyInseparable


/--
[exists_minpoly_X_pow_sub_C_of_finrank_eq_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PurelyInseparablePrimeDegree.lean)
-/
@[path]
private lemma exists_minpoly_X_pow_sub_C_of_finrank_eq_prime_eq
  [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L] [FiniteDimensional K L]
  {p : ℕ} [CharP K p]
-- given
  (hp : p.Prime)
  (hfin : finrank K L = p) :
-- imply
  ∃ α : L, ∃ a : K,
      minpoly K α = X ^ p - C a ∧
        (∀ b : K, b ^ p ≠ a) ∧ K⟮α⟯ = ⊤ := by
-- proof
  apply IsPurelyInseparable.exists_minpoly_X_pow_sub_C_of_finrank_eq_prime K L p hp hfin


-- created on 2026-10-20
