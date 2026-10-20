import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LucasSpecialPrime
open MetaMathlibExt


/--
[isLucasSpecialPrime_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasSpecialPrime.lean)
-/
@[path]
private lemma isLucasSpecialPrime_iff_eq
  {P Q : Int}
  {p : Nat} :
-- imply
  IsLucasSpecialPrime P Q p ↔ Nat.Prime p ∧ (p : Int) ∣ P ∧ (p : Int) ∣ Q := by
-- proof
  apply MetaMathlibExt.isLucasSpecialPrime_iff P Q p


-- created on 2026-10-20
