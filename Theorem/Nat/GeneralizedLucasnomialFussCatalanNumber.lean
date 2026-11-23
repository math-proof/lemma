module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.NumberTheory.GeneralizedLucasnomialFussCatalanNumber

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[generalizedLucasnomialFussCatalan_vol24_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucasnomialFussCatalanNumber.lean)
-/
@[path]
public theorem generalizedLucasnomialFussCatalan_vol24_eq
  {P : LucasParameters}
  {a r n : ℕ} :
-- imply
  generalizedLucasnomialFussCatalan P a r n =
    generalizedLucasnomialFussCatalanRS P a r n :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
