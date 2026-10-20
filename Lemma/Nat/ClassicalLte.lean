import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ClassicalLte
open MetaMathlibExt


/--
[padicValInt_pow_sub_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ClassicalLte.lean)
-/
@[path]
private lemma padicValInt_pow_sub_pow_eq
  {p : ℕ} [Fact (Nat.Prime p)]
  {a b : ℤ}
  {n : ℕ}
-- given
  (hodd : Odd p)
  (hne : a ≠ b)
  (hcop : ¬ (p : ℤ) ∣ a * b)
  (hdiv : (p : ℤ) ∣ a - b)
  (hn : n ≠ 0) :
-- imply
  padicValInt p (a ^ n - b ^ n) = padicValNat p n + padicValInt p (a - b) := by
-- proof
  apply MetaMathlibExt.padicValInt_pow_sub_pow p hodd hne hcop hdiv hn


-- created on 2026-10-20
