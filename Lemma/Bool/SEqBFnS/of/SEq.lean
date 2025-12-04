import stdlib.SEq
import sympy.Basic


@[main]
private lemma main
  {Vector : N → Sort v}
  {a : Vector n}
  {b : Vector n'}
  {g : N → N}
-- given
  (h : a ≃ b)
  (f : (n : N) → Vector n → Vector (g n)) :
-- imply
  f n a ≃ f n' b := by
-- proof
  let ⟨h_s, h⟩ := h
  constructor
  repeat congr


-- created on 2025-07-13
