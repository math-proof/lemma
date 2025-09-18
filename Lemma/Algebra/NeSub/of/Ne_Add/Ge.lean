import Lemma.Algebra.Ne_Sub.of.NeAdd.Ge
open Algebra


@[main]
private lemma main
  {x a b : ℕ}
-- given
  (h₀ : a ≥ b)
  (h1 : a ≠ x + b) :
-- imply
  a - b ≠ x :=
-- proof
  (Ne_Sub.of.NeAdd.Ge h₀ h1.symm).symm


@[main]
private lemma left
  {x a b : ℕ}
-- given
  (h₀ : a ≥ b)
  (h : a ≠ b + x) :
-- imply
  a - b ≠ x :=
-- proof
  (Ne_Sub.of.NeAdd.Ge.left h₀ h.symm).symm


-- created on 2025-06-11
