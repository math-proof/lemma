/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/SquareFreeWord.lean -/

import Mathlib.Data.List.Infix

/-!
Square-free words: finite and infinite words with no ordinary square factor,
including the ternary-alphabet and fixed-length specializations.

Sources:
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Khalyavin/khalyavin13.tex>,
<https://cs.uwaterloo.ca/journals/JIS/VOL4/GRIMM/words.tex>, and
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Sun/sun.tex>.
-/

namespace MetaMathlibExt

/-- An ordinary square: a word of the form `x ++ x` with `x` nonempty.
Source concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
def IsWordSquare {α : Type*} (w : List α) : Prop :=
  ∃ x : List α, x ≠ [] ∧ w = x ++ x

/-- A finite word is square-free if no factor is an ordinary square.
Source concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
def IsSquareFreeWord {α : Type*} (w : List α) : Prop :=
  ∀ s : List α, s.IsInfix w → ¬ IsWordSquare s

/-- An infinite word is square-free if it contains no adjacent equal blocks.
Source concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
def IsInfiniteSquareFreeWord {α : Type*} (u : Nat → α) : Prop :=
  ∀ i k : Nat, 0 < k → ∃ j, j < k ∧ u (i + j) ≠ u (i + k + j)

/-- The ternary alphabet `{a, b, c}`, represented as `Fin 3`.
Source concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
abbrev TernaryAlphabet := Fin 3

/-- A finite ternary word of length `n` is square-free in the ternary domain.
Source concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
def IsTernarySquareFreeLength (n : Nat) (w : List TernaryAlphabet) : Prop :=
  IsSquareFreeWord w ∧ w.length = n

/-- An infinite ternary word is square-free in the ternary domain.
Source concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
def IsInfiniteTernarySquareFreeWord (u : Nat → TernaryAlphabet) : Prop :=
  IsInfiniteSquareFreeWord u
end MetaMathlibExt
