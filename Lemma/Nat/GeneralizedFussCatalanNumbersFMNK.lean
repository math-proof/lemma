import Mathlib
import sympy.Basic
import Def.NumberTheory.GeneralizedFussCatalanNumbersFMNK
open MetaMathlibExt


namespace MetaMathlibExt

/--
[generalizedFussCatalanNumber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFussCatalanNumbersFMNK.lean)
-/
@[path]
lemma generalizedFussCatalanNumber_eq
  {m n k : ℕ} :
-- imply
  generalizedFussCatalanNumber m n k =
      k * Nat.choose (m * n + k) n / (m * n + k) :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[generalizedFussCatalanNumber_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFussCatalanNumbersFMNK.lean)
-/
@[path]
lemma generalizedFussCatalanNumber_one
  {m k : ℕ} :
-- imply
  generalizedFussCatalanNumber m 1 k = k := by
-- proof
  unfold generalizedFussCatalanNumber
  have hmk : m * 1 + k = m + k := by omega
  rw [hmk, Nat.choose_one_right]
  by_cases h : m + k = 0
  · have hk : k = 0 := by omega
    simp [hk]
  · have hpos : 0 < m + k := by omega
    exact Nat.mul_div_cancel k hpos

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
