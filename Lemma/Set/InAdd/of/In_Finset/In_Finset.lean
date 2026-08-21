import Lemma.Set.In_Finset.is.OrEqS
open Set


@[main]
private lemma main
  [Add α]
  {x0 x1 a b c d : α}
-- given
  (h0 : x0 ∈ ({a, b} : Set α))
  (h1 : x1 ∈ ({c, d} : Set α)) :
-- imply
  x0 + x1 ∈ ({a + c, a + d, b + c, b + d} : Set α) := by
-- proof
  rcases OrEqS.of.In_Finset h1 with h1 | h1
  ·
    rcases OrEqS.of.In_Finset h0 with h0 | h0
    ·
      simp [h0, h1]
    ·
      simp [h0, h1]
  ·
    rcases OrEqS.of.In_Finset h0 with h0 | h0
    ·
      simp [h0, h1]
    ·
      simp [h0, h1]


-- created on 2018-11-18
-- updated on 2026-08-21
