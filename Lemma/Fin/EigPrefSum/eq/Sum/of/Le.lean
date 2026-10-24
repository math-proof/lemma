import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.KyFan
open InnerProductSpace.KyFanWanted


/--
[KyFan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/KyFan.lean)
-/
@[path]
private lemma eig_pref_sum_eq_sum_eq
-- given
  {n : ℕ}
  (k : ℕ)
  (hk : k ≤ n)
  (eig : Fin n → ℝ) :
-- imply
  eigPrefSum eig k hk = ∑ i : Fin k, eig (Fin.castLE hk i) := by
-- proof
  apply InnerProductSpace.KyFanWanted.eigPrefSum_eq_sum eig k hk


-- created on 2026-10-24
