import Macro.Order.ExprWithLimits
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f g : ℝ → ℝ}
-- given
  (h : ∀ x ∈ S, f x = g x) :
-- imply
  max⁻¹[x ∈ S] f x = max⁻¹[x ∈ S] g x := by
-- proof
  unfold «max⁻¹»
  congr 1
  funext x
  apply propext
  constructor
  ·
    rintro ⟨hx, hy⟩
    exact ⟨hx, fun y hy' => by rw [← h y hy', ← h x hx]; exact hy y hy'⟩
  ·
    rintro ⟨hx, hy⟩
    exact ⟨hx, fun y hy' => by rw [h y hy', h x hx]; exact hy y hy'⟩


-- created on 2019-01-07
-- updated on 2026-10-26
