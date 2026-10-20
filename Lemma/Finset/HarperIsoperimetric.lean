import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.HarperIsoperimetric
open MathlibExt.Combinatorics.HarperIsoperimetricWanted


/--
[harper_isoperimetric_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/HarperIsoperimetric.lean)
-/
@[path]
private lemma harper_isoperimetric_inequality_eq
  {n : ℕ}
  {A B : Finset (Fin n → Bool)}
  {t : ℕ}
-- given
  (hB : Hamming.IsBall B)
  (hcard : B.card ≤ A.card)
  (ht : 0 < t) :
-- imply
  (Hamming.expansion B t).card ≤ (Hamming.expansion A t).card := by
-- proof
  apply MathlibExt.Combinatorics.HarperIsoperimetricWanted.harper_isoperimetric_inequality A B hB hcard t ht


-- created on 2026-10-20
