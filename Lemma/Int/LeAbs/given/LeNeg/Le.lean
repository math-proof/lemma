import Lemma.Int.LeAbs.is.LeNeg.Le
open Int


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x d : α}
-- given
  (h : |x| ≤ d) :
-- imply
  x ≤ d ∧ -d ≤ x := by
-- proof
  have ⟨h₀, h₁⟩ := LeNeg.Le.of.LeAbs (x := x) (d := d) h
  exact ⟨h₁, h₀⟩


-- created on 2026-10-03
