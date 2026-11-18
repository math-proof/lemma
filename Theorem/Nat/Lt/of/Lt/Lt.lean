module

public import Mathlib

public section


/--
This lemma establishes the transitivity of the less-than relation in a preorder.
Given elements `a < b` and `b < c`, it concludes `a < c` by applying the transitivity property of the preorder's ordering relation.
-/
public theorem Nat.Lt.of.Lt.Lt
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a < b)
  (h₁ : b < c) :
-- imply
  a < c :=
-- proof
  lt_trans h₀ h₁


public theorem Nat.Lt.of.Lt.Lt.subst
  {y b x t k : ℝ}
-- given
  (hk : k > 0)
  (h₀ : y < x * k + b)
  (h₁ : x < t) :
-- imply
  y < t * k + b := by
-- proof
  nlinarith


-- created on 2018-10-11
-- updated on 2026-10-26
-- updated on 2026-09-27
