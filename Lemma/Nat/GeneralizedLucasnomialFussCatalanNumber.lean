import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedLucasnomialFussCatalanNumber
open MetaMathlibExt


/--
[generalizedLucasnomialFussCatalan_vol24_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucasnomialFussCatalanNumber.lean)
-/
@[path]
private lemma generalizedLucasnomialFussCatalan_vol24_eq_eq
  {P : LucasParameters}
  {a r n : ℕ} :
-- imply
  generalizedLucasnomialFussCatalan P a r n =
    generalizedLucasnomialFussCatalanRS P a r n := by
-- proof
  apply MetaMathlibExt.generalizedLucasnomialFussCatalan_vol24_eq P a r n


-- created on 2026-10-20
