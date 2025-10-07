import Lemma.Bool.And_Or.is.OrAndS
import Lemma.Bool.AndAnd__Not.is.False
open Bool


@[main, comm, mp, mpr]
private lemma main :
-- imply
  ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
-- proof
  constructor
  · 
    intro h
    by_contra h_NotOr
    apply h_NotOr
    apply Or.inr
    intro hq
    apply h_NotOr
    apply Or.inl
    intro hpq
    apply h
    apply And.intro
    exact hpq
    exact hq
  · 
    intro h hpq
    have h := And.intro hpq h
    rw [And_Or.is.OrAndS] at h
    simp [
      AndAnd__Not.is.False true,
      AndAnd__Not.is.False false
    ] at h


-- created on 2024-07-01
-- updated on 2025-07-30
