import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.of_Nat_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {n:ℕ} :
-- imply
  (OfNat.ofNat n:Section_4_2.Rat) = (OfNat.ofNat n:Nat) // 1 :=
-- proof
  Section_4_2.Rat.of_Nat_eq n


-- created on 2026-10-22
-- updated on 2026-10-23
