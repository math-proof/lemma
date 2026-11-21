import Theorem.Nat.Ne_0.of.Lt0Mul
import Initialize.Tactic.Attr.Basic
open Nat


@[path]
private lemma left
  {a b : ℕ}
-- given
  (h : a * b > 0) :
-- imply
  a > 0 := by
-- proof
  have := Ne_0.of.Lt0Mul.left h
  apply Nat.pos_of_ne_zero this

@[path]
private lemma main
  {a b : ℕ}
-- given
  (h : a * b > 0) :
-- imply
  b > 0 := by
-- proof
  have := Ne_0.of.Lt0Mul h
  apply Nat.pos_of_ne_zero this


-- created on 2025-06-13
-- updated on 2026-11-21
