import sympy.Basic


@[path]
private lemma main
  {A : Set ι} [DecidablePred (· ∈ A)]
  {f : ι → Set α} :
-- imply
  (⋂ x ∈ A, f x) = ⋂ x, if x ∈ A then f x else Set.univ := by
-- proof
  ext y
  aesop


-- created on 2026-10-11
-- updated on 2026-10-17
