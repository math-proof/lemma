/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FussCatalanNumber.lean -/

import Mathlib.Data.Nat.Choose.Basic

namespace MetaMathlibExt

/-- The Fuss–Catalan number
`Nat.choose (k * m) m / ((k - 1) * m + 1)` for positive chord arity `k`.

Concepts `jis_term_ebafb51c3672353ca538423c` and
`jis_sem_1faa20d56755b6a211607da7`; source JIS VOL23/Young,
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Young/young5.tex>,
SHA-256 `5c6d6c8dc8aae4faa4a889e2251d51792c3ca6bc95285880041806013bf413bd`. -/
def fussCatalanNumber (k m : ℕ) (_hk : 1 ≤ k) : ℕ :=
  Nat.choose (k * m) m / ((k - 1) * m + 1)

end MetaMathlibExt
