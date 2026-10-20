import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PowerSumVanishing
open MetaMathlibExt


/--
[powerSum_vanishing_mod_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerSumVanishing.lean)
-/
@[path]
private lemma powerSum_vanishing_mod_prime_eq
  {p e : ℕ}
-- given
  (hp : Nat.Prime p)
  (he : 1 ≤ e → ¬ (p - 1) ∣ e) :
-- imply
  (p : ℤ) ∣ ∑ t ∈ Finset.Icc 1 p, (t : ℤ) ^ e := by
-- proof
  apply MetaMathlibExt.powerSum_vanishing_mod_prime p hp e he


-- created on 2026-10-20
