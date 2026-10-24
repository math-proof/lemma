import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.not_P_3_3_3b_existsUnique](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory] :
-- imply
  ¬ ∀ x, ∃! y: Chapter3.Nat, P_3_3_3b x y :=
-- proof
  by
    by_contra h
    choose n hn _ using h (0:Chapter3.Nat)
    have : ((0:Chapter3.Nat):ℕ) = 0 := by simp [OfNat.ofNat]
    simp [P_3_3_3b, this] at hn


-- created on 2026-10-22
-- updated on 2026-10-23
