/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/RStirlingFirstAlternatingExpansion.lean -/


import Def.Combinatorics.Enumerative.RStirlingFirstAlternatingExpansion
import Lemma.Finset.Enumerative.RStirlingFirstAlternatingExpansion


namespace MetaMathlibExt

example : rStirlingFirst 2 2 2 = 1 := by simp [rStirlingFirst_self]

example : rStirlingFirst 2 1 2 = 0 := by simp [rStirlingFirst_self]

example : rStirlingFirst 5 0 2 = 0 := rStirlingFirst_zero_of_pos 5 2 (by omega)

example : rStirlingFirst 3 2 2 = 2 := by
  rw [rStirlingFirst_succ 2 2 2 (by omega) le_rfl]
  simp [rStirlingFirst_self]

end MetaMathlibExt
