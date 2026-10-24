/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GeneralizedFussCatalanNumbersFMNK.lean -/


import sympy.atlas.NumberTheory.GeneralizedFussCatalanNumbersFMNK
import Lemma.Nat.GeneralizedFussCatalanNumbersFMNK

namespace MetaMathlibExt

example : generalizedFussCatalanNumber 2 3 1 = 5 := by decide

example : generalizedFussCatalanNumber 3 2 1 = 3 := by decide

example : generalizedFussCatalanNumber 7 1 4 = 4 := by decide

example : generalizedFussCatalanNumber 2 0 1 = 1 := by decide

example (m k : ℕ) : generalizedFussCatalanNumber m 1 k = k :=
  generalizedFussCatalanNumber_one m k

end MetaMathlibExt
