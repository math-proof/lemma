import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.CauchySequence


/--
[CauchySequence.equiv_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a b: CauchySequence} :
-- imply
  a ≈ b ↔ Sequence.Equiv a b :=
-- proof
  Chapter5.CauchySequence.equiv_iff a b


-- created on 2026-10-22
