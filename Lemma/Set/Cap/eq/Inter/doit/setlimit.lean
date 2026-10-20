import sympy.Basic


@[path]
private lemma main
  {s : Set ι} [DecidablePred (· ∈ s)]
  {t : ι → Set κ} [∀ i, DecidablePred (· ∈ t i)]
  {f : ι → κ → Set α} :
-- imply
  (⋂ i ∈ s, ⋂ j ∈ t i, f i j) =
    ⋂ i, ⋂ j, if i ∈ s ∧ j ∈ t i then f i j else Set.univ := by
-- proof
  ext x
  simp
  grind


-- created on 2021-01-17
-- updated on 2026-10-17
