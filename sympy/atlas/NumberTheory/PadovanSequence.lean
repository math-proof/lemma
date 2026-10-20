/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PadovanSequence.lean -/

import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

/-- The shifted Padovan sequence with initial values `1, 0, 1` and recurrence
`a_(n+3) = a_(n+1) + a_n`.

This is the shifted version used by Daniel Birmajer, Juan B. Gil, and Michael D. Weiner in
*Linear Recurrence Sequences and Their Convolutions via Bell Polynomials*,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Gil/gil3.tex>.

JIS concept: `jis_sem_2d63874aa161ff9e950867e1`.
-/
def shiftedPadovanSequence : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | n + 3 => shiftedPadovanSequence (n + 1) + shiftedPadovanSequence n

@[simp] theorem shiftedPadovanSequence_zero : shiftedPadovanSequence 0 = 1 := rfl

@[simp] theorem shiftedPadovanSequence_one : shiftedPadovanSequence 1 = 0 := rfl

@[simp] theorem shiftedPadovanSequence_two : shiftedPadovanSequence 2 = 1 := rfl

/-- The defining recurrence of the shifted Padovan sequence. -/
theorem shiftedPadovanSequence_add_three (n : Nat) :
    shiftedPadovanSequence (n + 3) =
      shiftedPadovanSequence (n + 1) + shiftedPadovanSequence n := rfl

end MetaMathlibExt
