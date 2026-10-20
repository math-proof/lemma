import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.LucasSequenceFirstKind
open MetaMathlibExt


/--
[IsLucasSequenceFirstKind.initialZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasSequenceFirstKind.lean)
-/
@[path]
private lemma IsLucasSequenceFirstKind_initialZero_eq
  {P Q : ℤ}
  {u : ℕ → ℤ}
-- given
  (h : IsLucasSequenceFirstKind P Q u) :
-- imply
  u 0 = 0 := by
-- proof
  apply MetaMathlibExt.IsLucasSequenceFirstKind.initialZero h

/--
[IsLucasSequenceFirstKind.initialOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasSequenceFirstKind.lean)
-/
@[path]
private lemma IsLucasSequenceFirstKind_initialOne_eq
  {P Q : ℤ}
  {u : ℕ → ℤ}
-- given
  (h : IsLucasSequenceFirstKind P Q u) :
-- imply
  u 1 = 1 := by
-- proof
  apply MetaMathlibExt.IsLucasSequenceFirstKind.initialOne h

/--
[IsLucasSequenceFirstKind.recurrenceStep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasSequenceFirstKind.lean)
-/
@[path]
private lemma IsLucasSequenceFirstKind_recurrenceStep_eq
  {P Q : ℤ}
  {u : ℕ → ℤ}
  {n : ℕ}
-- given
  (h : IsLucasSequenceFirstKind P Q u) :
-- imply
  u (n + 2) = P * u (n + 1) - Q * u n := by
-- proof
  apply MetaMathlibExt.IsLucasSequenceFirstKind.recurrenceStep h n


-- created on 2026-10-20
