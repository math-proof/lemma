/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/GeneralizedRascalTriangle.lean -/


import Def.Combinatorics.Enumerative.GeneralizedRascalTriangle


namespace MetaMathlibExt

example (c d d₁ d₂ : ℤ) :
    IsGeneralizedRascalTriangle fun r k =>
      c + (k : ℤ) * d₁ + (r : ℤ) * d₂ + (r : ℤ) * (k : ℤ) * d := by
  exact ⟨c, d, d₁, d₂, fun _ _ => rfl⟩

end MetaMathlibExt
