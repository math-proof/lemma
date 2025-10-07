import Lemma.Bool.And_Or.is.OrAndS
open Bool


@[main, comm, mp, mpr]
private lemma main :
-- imply
  (q ∨ r) ∧ p ↔ q ∧ p ∨ r ∧ p := by
-- proof
  rw [And.comm]
  rw [And_Or.is.OrAndS]
  rw [And.comm]
  rw [And.comm (b := r)]


@[main, comm, mp, mpr]
private lemma apart:
-- imply
  (q ∨ r) ∧ p ↔ p ∧ q ∨ r ∧ p := by
-- proof
  simp [OrAndS.is.And_Or.apart]
  rw [And.comm]


-- created on 2024-07-01
