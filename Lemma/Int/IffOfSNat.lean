import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_4_1.Part8
open Section_4_1 hiding Int
open Section_4_1.Int


/--
[Int.ofNat_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {n m:ℕ} :
-- imply
  (OfNat.ofNat n : Section_4_1.Int) = (OfNat.ofNat m : Section_4_1.Int) ↔ OfNat.ofNat n = OfNat.ofNat m :=
-- proof
  Section_4_1.Int.ofNat_inj n m


-- created on 2026-10-22
-- updated on 2026-10-26
