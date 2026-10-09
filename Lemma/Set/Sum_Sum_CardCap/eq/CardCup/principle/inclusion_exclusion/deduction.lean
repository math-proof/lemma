import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import sympy.Basic



@[path]
private lemma main
  [DecidableEq α]
  {n : ℕ}
  {A : Fin n → Finset α} :
-- imply
  (Finset.univ.biUnion A).card =
    ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (·.Nonempty)).attach,
      (-1 : ℤ) ^ (S.val.card + 1) * (Finset.inf' S.val (Finset.mem_filter.mp S.property).2 A).card :=
-- proof
  Finset.inclusion_exclusion_card_biUnion (s := Finset.univ) (S := A)


-- created on 2026-10-07
