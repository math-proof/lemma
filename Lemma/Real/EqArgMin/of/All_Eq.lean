import Syntax.Order.ExprWithLimits
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f g : ℝ → ℝ}
-- given
  (h : ∀ x ∈ S, f x = g x) :
-- imply
  min⁻¹[x ∈ S] f x = min⁻¹[x ∈ S] g x := by
-- proof
  unfold «min⁻¹»
  congr 1
  funext x
  apply propext
  constructor
  ·
    rintro ⟨hx, hy⟩
    exact ⟨hx, fun y hy' => by rw [← h x hx, ← h y hy']; exact hy y hy'⟩
  ·
    rintro ⟨hx, hy⟩
    exact ⟨hx, fun y hy' => by rw [h x hx, h y hy']; exact hy y hy'⟩


-- created on 2019-01-08
