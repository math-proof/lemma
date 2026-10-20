import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.CarlitzBlockHarmonic


/--
[ZMod.carlitz_sum_inv_block_Ico_eq_zero_of_five_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CarlitzBlockHarmonic.lean)
-/
@[path]
private lemma ZMod_carlitz_sum_inv_block_Ico_eq_zero_of_five_le_eq
  {p k : ℕ}
-- given
  (hp : p.Prime)
  (hp5 : 5 ≤ p) :
-- imply
  (Finset.Ico 1 p).sum
    (fun r => (((k * p + r : ℕ) : ZMod (p ^ 2))⁻¹)) = 0 := by
-- proof
  apply ZMod.carlitz_sum_inv_block_Ico_eq_zero_of_five_le p k hp hp5


-- created on 2026-10-20
