/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AeratedCentralBinomialNumber.lean -/

import Mathlib.Data.Nat.Choose.Basic

/-!
# Aerated central binomial numbers

Source: Paul Barry and A. Mesinga Mwafise, *Classical and Semi-Classical
Orthogonal Polynomials Defined by Riordan Arrays, and Their Moment Sequences*,
Journal of Integer Sequences 21 (2018), Article 18.1.5.
-/

namespace MetaMathlibExt

/-- The aerated central binomial sequence `1, 0, 2, 0, 6, 0, 20, ...`.

Stable source identifiers: concept `jis_sem_7b40d8a9f9fe5eaa13955a5f`,
statement `jis_f04d18af371ba88dde3aabdc`.
-/
def aeratedCentralBinomialNumber (n : ℕ) : ℕ :=
  if n % 2 = 0 then Nat.choose n (n / 2) else 0

end MetaMathlibExt
