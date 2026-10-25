/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CipollaPseudoprime.lean -/

import Mathlib.NumberTheory.FermatPsp
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star


namespace MetaMathlibExt

def psp_from_prime (b : ℕ) (p : ℕ) : ℕ :=
  (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1))

end MetaMathlibExt
