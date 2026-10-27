import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Recurrences.LucasSequenceFirstKind
open MetaMathlibExt


namespace MetaMathlibExt

/--
[IsLucasSequenceFirstKind.initialZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasSequenceFirstKind.lean)
-/
@[path]
lemma IsLucasSequenceFirstKind.initialZero
  {P Q : ℤ}
  {u : ℕ → ℤ}
-- given
  (h : IsLucasSequenceFirstKind P Q u) :
-- imply
  u 0 = 0 :=
-- proof
  h.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsLucasSequenceFirstKind.initialOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasSequenceFirstKind.lean)
-/
@[path]
lemma IsLucasSequenceFirstKind.initialOne
  {P Q : ℤ}
  {u : ℕ → ℤ}
-- given
  (h : IsLucasSequenceFirstKind P Q u) :
-- imply
  u 1 = 1 :=
-- proof
  h.2.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsLucasSequenceFirstKind.recurrenceStep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasSequenceFirstKind.lean)
-/
@[path]
lemma IsLucasSequenceFirstKind.recurrenceStep
  {P Q : ℤ}
  {u : ℕ → ℤ}
  {n : ℕ}
-- given
  (h : IsLucasSequenceFirstKind P Q u) :
-- imply
  u (n + 2) = P * u (n + 1) - Q * u n :=
-- proof
  h.2.2 n

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
