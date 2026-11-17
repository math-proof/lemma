module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Def.Algebra.Polynomial.UnsignedCharlierPolynomialsOfOrder0

public section

namespace MetaMathlibExt

/-- General coefficient equality for the natural rows. -/
theorem unsignedCharlier_coeff_eq (n m : ℕ) :
    (unsignedCharlierOrder0 ℕ n).coeff m = unsignedCharlierCoeff n m := by
  simp [unsignedCharlierOrder0, unsignedCharlierCoeff]

end MetaMathlibExt
