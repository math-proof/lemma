import Def.Algebra.ContinuedFractions.ContinuedFraction
open Continuant


@[path]
private lemma main
  [Field R]
-- given
  (c : R) :
-- imply
  ∀ {m : List R}, m ≠ [] → alpha (c :: m) = c + 1 / alpha m := by
-- proof
  intro p₀ p₁
  match p₀, p₁ with
  | _ :: _, _ => rfl


-- created on 2026-10-07
