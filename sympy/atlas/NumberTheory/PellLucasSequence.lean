/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PellLucasSequence.lean -/

import Mathlib.Data.Nat.Basic

/-!
# Pell–Lucas numbers

This module uses the associated-Pell convention `1, 1, 3, 7, 17, …` for OEIS A001333.

JIS concept: `jis_sem_42455744e467dce308e4961b`.
-/

namespace MetaMathlibExt

/-- The Pell–Lucas (associated Pell) sequence `1, 1, 3, 7, 17, …` (OEIS A001333).

Source: aBa Mbirika, Janee Schrader, and Jürgen Spilker, *Pell and Associated Pell Braid
Sequences as GCDs of Sums of k Consecutive Pell, Balancing, and Related Numbers*,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Mbirika/mbir5.tex>.
-/
def pellLucasSequence : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * pellLucasSequence (n + 1) + pellLucasSequence n

@[simp] theorem pellLucasSequence_zero : pellLucasSequence 0 = 1 := rfl

@[simp] theorem pellLucasSequence_one : pellLucasSequence 1 = 1 := rfl

/-- The defining recurrence of the Pell–Lucas sequence. -/
theorem pellLucasSequence_succ_succ (n : ℕ) :
    pellLucasSequence (n + 2) =
      2 * pellLucasSequence (n + 1) + pellLucasSequence n := rfl

end MetaMathlibExt
