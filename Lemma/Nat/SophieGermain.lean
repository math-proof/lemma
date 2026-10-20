import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SophieGermain
open MetaMathlibExt


/--
[sophieGermain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SophieGermain.lean)
-/
@[path]
private lemma sophieGermain_eq
  {p x y z : ℕ} :
-- imply
  Odd p → Nat.Prime p → Nat.Prime (2 * p + 1) →
    0 < x → 0 < y → 0 < z →
    Nat.Coprime x y → Nat.Coprime y z → Nat.Coprime x z →
    x ^ p + y ^ p = z ^ p → p ∣ x * y * z := by
-- proof
  apply MetaMathlibExt.sophieGermain p x y z


-- created on 2026-10-20
