/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CFiniteSequence.lean -/

import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.Order


namespace MetaMathlibExt

/-- An integer sequence is C-finite if it eventually satisfies a fixed
constant-coefficient linear recurrence.

Concept `jis_term_8dfeefcfa70ce96efa8b4fb3`; source JIS VOL26/Fischer–Kotek–Makowsky,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Makowsky/makowsky16.tex>, lines 249–259. -/
def IsIntegerCFiniteSequence (s : ℕ → ℤ) : Prop :=
  ∃ p q, ∃ c : Fin p → ℤ, ∀ n, q ≤ n → s (n + p) = ∑ i, c i * s (n + (i : ℕ))

end MetaMathlibExt
