import sympy.sets.fancysets
import Lemma.Int.In_Range.is.Mod.In_Range


@[main]
private lemma main
  {x a b d : ℤ}
-- given
  (h : x ∈ Range a b d) :
-- imply
  x ∈ Range a b (Int.sign d) ∧ x % d = a % d := by
-- proof
  exact and_comm.mp (Int.In_Range.is.Mod.In_Range.mp h)


-- created on 2023-05-30
