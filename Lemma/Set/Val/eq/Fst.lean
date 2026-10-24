import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.pair_eq_fst_snd](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {z:X ×ˢ Y} :
-- imply
  z.val = (⟨ fst z, snd z ⟩:OrderedPair) :=
-- proof
  Chapter3.SetTheory.Set.pair_eq_fst_snd z


-- created on 2026-10-22
