import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma both
  {n : ℕ}
  {f g : ℕ → Set ℝ}
-- given
  (h : ∀ i, f i ⊆ g i) :
-- imply
  ⋃ i < n, f i ⊆ ⋃ i < n, g i := by
-- proof
  exact Set.iUnion₂_mono fun i _ => h i


@[path]
private lemma lhs
  {n m : ℕ}
  {x : ℕ → Set (Fin n → ℂ)}
  {A : Set (Fin n → ℂ)}
-- given
  (h : ∀ i, x i ⊆ A) :
-- imply
  ⋃ i < m, x i ⊆ A := by
-- proof
  exact Set.iUnion₂_subset fun i _ => h i


-- created on 2021-06-28
