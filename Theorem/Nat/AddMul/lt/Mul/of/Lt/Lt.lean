module

public import Theorem.Nat.AddMul.lt.Mul.of.Lt
public import Initialize.Tactic.Attr.Basic

public section

open Nat


@[path]
private lemma main
  {m n : ℕ}
-- given
  (h₀ : i < m)
  (h₁ : j  < n) :
-- imply
  i * n + j < m * n := by
-- proof
  let j : Fin n := ⟨j, h₁⟩
  have := AddMul.lt.Mul.of.Lt h₀ j
  simp_all
  assumption


-- created on 2025-06-14
