import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedFussCatalanNumbersFMNK
open MetaMathlibExt


/--
[generalizedFussCatalanNumber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFussCatalanNumbersFMNK.lean)
-/
@[path]
private lemma generalizedFussCatalanNumber_eq_eq
  {m n k : ℕ} :
-- imply
  generalizedFussCatalanNumber m n k =
      k * Nat.choose (m * n + k) n / (m * n + k) := by
-- proof
  apply MetaMathlibExt.generalizedFussCatalanNumber_eq m n k

/--
[generalizedFussCatalanNumber_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFussCatalanNumbersFMNK.lean)
-/
@[path]
private lemma generalizedFussCatalanNumber_one_eq
  {m k : ℕ} :
-- imply
  generalizedFussCatalanNumber m 1 k = k := by
-- proof
  apply MetaMathlibExt.generalizedFussCatalanNumber_one m k


-- created on 2026-10-20
