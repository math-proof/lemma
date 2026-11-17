/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CipollaPseudoprime.lean -/

module

public import Mathlib.NumberTheory.FermatPsp
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

@[expose] public section

namespace MetaMathlibExt

def psp_from_prime (b : ℕ) (p : ℕ) : ℕ :=
  (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1))

end MetaMathlibExt
