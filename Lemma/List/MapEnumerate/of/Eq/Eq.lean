import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {f g : α → ℕ → β}
  {a b : List α}
-- given
  (h₀ : a = b)
  (h₁ : f = g) :
-- imply
  (a.enumerate.map (fun args => f args.2 args.1)) = b.enumerate.map (fun args => g args.2 args.1) := by
-- proof
  aesop


-- created on 2025-06-02
