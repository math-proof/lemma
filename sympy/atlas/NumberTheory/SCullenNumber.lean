/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SCullenNumber.lean -/

import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

/-- The `s`-Cullen value `C_{n,s} = n * s ^ n + 1`.

Source: Jon Grantham and Hester Graves, *The abc Conjecture Implies That Only Finitely Many
s-Cullen Numbers Are Repunits*, Journal of Integer Sequences 24 (2021),
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Grantham/gran4.tex>.

JIS concept: `jis_sem_281a433c6542caee86b48369`; defining statement:
`jis_0272eab809344ae92672f303`.
-/
def sCullenNumber (s n : ℕ) : ℕ := n * s ^ n + 1

/-- A number `m` is an `s`-Cullen number for base `s` when `2 ≤ s` and
`m = C_{n,s}` for some positive `n`.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL24/Grantham/gran4.tex>.
-/
def IsSCullenNumber (s m : ℕ) : Prop :=
  2 ≤ s ∧ ∃ n, 0 < n ∧ sCullenNumber s n = m

end MetaMathlibExt
