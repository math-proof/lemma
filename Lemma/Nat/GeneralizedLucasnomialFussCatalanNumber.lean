import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedLucasnomialFussCatalanNumber
open MetaMathlibExt


namespace MetaMathlibExt

/--
[generalizedLucasnomialFussCatalan_vol24_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucasnomialFussCatalanNumber.lean)
-/
@[path]
lemma generalizedLucasnomialFussCatalan_vol24_eq
  {P : LucasParameters}
  {a r n : ℕ} :
-- imply
  generalizedLucasnomialFussCatalan P a r n =
    generalizedLucasnomialFussCatalanRS P a r n :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
