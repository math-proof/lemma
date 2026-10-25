import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_707.Part5
open IsPerfectDifferenceSet


/--
[IsPerfectDifferenceSet.card](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  {N: ℕ} [NeZero N]
  {B: Finset (ZMod N)}
-- given
  (hdiff: IsPerfectDifferenceSet B) :
-- imply
  B.card * B.card + 1 = N + B.card :=
-- proof
  IsPerfectDifferenceSet.card hdiff


-- created on 2026-10-22
