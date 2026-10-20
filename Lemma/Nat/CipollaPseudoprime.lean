import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.CipollaPseudoprime
open MetaMathlibExt


/--
[cipolla_pseudoprime_construction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CipollaPseudoprime.lean)
-/
@[path]
private lemma cipolla_pseudoprime_construction_eq
  {a p : ℕ}
-- given
  (ha : 1 < a)
  (hp : p.Prime)
  (hnotdvd : ¬ p ∣ a * (a ^ 2 - 1)) :
-- imply
  let n₁ := by
-- proof
  apply MetaMathlibExt.cipolla_pseudoprime_construction a p ha hp hnotdvd


-- created on 2026-10-20
