import sympy.sets.sets
import sympy.Basic


@[path]
private lemma inner_subs
  {n m : ℕ}
  {f g : (Fin n → ℂ) → (Fin m → ℂ)}
  {h : (Fin n → ℂ) → ℝ} :
-- imply
  f '' {x | f x = g x ∧ h x > 0} = g '' {x | f x = g x ∧ h x > 0} := by
-- proof
  exact Set.image_congr fun _ hx => hx.1


-- created on 2020-07-10
