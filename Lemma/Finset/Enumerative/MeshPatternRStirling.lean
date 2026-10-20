import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MeshPatternRStirling
open MetaMathlibExt


/--
[meshPatternCount_eq_factorial_mul_rStirlingNumber_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma meshPatternCount_eq_factorial_mul_rStirlingNumber_general_eq
  {n k j : ℕ}
-- given
  (hkn : k ≤ n)
  (hk : 2 ≤ k) :
-- imply
  Fintype.card {σ : Equiv.Perm (Fin n) // meshN k σ = j} =
    (k - 1).factorial * rStirlingFirst n (j + k - 1) (k - 1) := by
-- proof
  apply MetaMathlibExt.meshPatternCount_eq_factorial_mul_rStirlingNumber_general n k j hkn hk

/--
[meshPatternCount_eq_factorial_mul_rStirlingNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma meshPatternCount_eq_factorial_mul_rStirlingNumber_eq
  {n k j : ℕ}
-- given
  (hkn : k ≤ n)
  (hk : 2 ≤ k) :
-- imply
  let isLeftToRightMaximum := by
-- proof
  apply MetaMathlibExt.meshPatternCount_eq_factorial_mul_rStirlingNumber n k j hkn hk


-- created on 2026-10-20
