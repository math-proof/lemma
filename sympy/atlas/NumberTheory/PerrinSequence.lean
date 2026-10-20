/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PerrinSequence.lean -/

import Mathlib.Data.Nat.Basic

/-!
# Perrin sequence

Sources:
<https://cs.uwaterloo.ca/journals/JIS/VOL11/Marichal/marichal.tex>,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/MacHenry/machenry7.tex>, and
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Togbe/togbe16.tex>.
-/

namespace MetaMathlibExt

/-- Perrin sequence (`jis_sem_4f37e8f82153e07bac03f158`; statements
`jis_013645d8a02b3ef65aa100f4`, `jis_4a7feefed2ca398758f666fc`, and
`jis_6027c59af02d1d1dfc3e7b1a`): the sequence `Eₙ` with `E 0 = 3`,
`E 1 = 0`, `E 2 = 2`, and `E n = E (n - 2) + E (n - 3)` for `n ≥ 3`. -/
def perrinSequence : Nat → Nat
  | 0 => 3
  | 1 => 0
  | 2 => 2
  | (n + 3) => perrinSequence (n + 1) + perrinSequence n

end MetaMathlibExt
