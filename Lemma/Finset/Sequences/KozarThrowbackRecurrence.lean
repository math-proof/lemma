import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Sequences.KozarThrowbackRecurrence
open MetaMathlibExt


/--
[kozar_throwback_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/KozarThrowbackRecurrence.lean)
-/
@[path]
private lemma kozar_throwback_recurrence_eq
  :
-- imply
  let throwbackStep : (ℕ → ℕ) → (ℕ → ℕ) := by
-- proof
  apply MetaMathlibExt.kozar_throwback_recurrence


-- created on 2026-10-20
