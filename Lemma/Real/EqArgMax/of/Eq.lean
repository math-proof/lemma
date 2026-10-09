import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : ∀ i ∈ S, f i = g i) :
-- imply
  ArgMax S f = ArgMax S g := by
-- proof
  unfold ArgMax
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hx, fun y hy' => by rw [← h y hy', ← h x hx]; exact hy y hy'⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, fun y hy' => by rw [h y hy', h x hx]; exact hy y hy'⟩


@[path]
private lemma definition
  {x₀ : ℝ}
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : ∃ x ∈ S, ∀ y ∈ S, f y ≤ f x)
  (h : x₀ = ArgMax S f) :
-- imply
  f x₀ = Maxima S f := by
-- proof
  subst h
  have hs := Classical.epsilon_spec h₀
  exact (IsGreatest.csSup_eq ⟨Set.mem_image_of_mem f hs.1, by rintro _ ⟨y, hy, rfl⟩; exact hs.2 y hy⟩).symm


-- created on 2019-04-04
