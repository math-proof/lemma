import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_4_1.Part8
open Section_4_1 hiding Int
open Section_4_1.Int


/--
[Int.natCast_ofNat](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {n:ℕ} :
-- imply
  ((OfNat.ofNat n:ℕ): Section_4_1.Int) = OfNat.ofNat n :=
-- proof
  Section_4_1.Int.natCast_ofNat n


-- created on 2026-10-22
-- updated on 2026-10-26
