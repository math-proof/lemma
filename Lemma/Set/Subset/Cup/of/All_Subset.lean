import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → Set ℤ}
-- given
  (h : ∀ i < n, f i ⊆ g i) :
-- imply
  ⋃ i < n, f i ⊆ ⋃ i < n, g i := by
-- proof
  exact Set.iUnion₂_mono h


-- created on 2020-08-03
