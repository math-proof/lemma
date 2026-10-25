/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SternSequence.lean -/

import Mathlib.Data.Nat.Basic


namespace MetaMathlibExt

/-- Stern sequence (`jis_term_8e87f9eebae5b6160acdc06a`, "Stern diatomic sequence",
OEIS A002487): the function `s : Nat → Nat` with `s 0 = 0`, `s 1 = 1`,
`s (2 * n) = s n` and `s (2 * n + 1) = s n + s (n + 1)` for `n ≥ 1`
(JIS Lansing, lines 92-103; JIS Dennison, lines 80-85). -/
def sternSequence : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if h : (n + 2) % 2 = 0 then sternSequence ((n + 2) / 2)
    else sternSequence ((n + 2) / 2) + sternSequence ((n + 2) / 2 + 1)
termination_by n => n
decreasing_by all_goals omega

end MetaMathlibExt
