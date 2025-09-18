import Lemma.Logic.OrOr.is.Or_Or
import Lemma.Logic.AndOr.is.OrAndS
open Logic


@[main]
private lemma main
-- given
  (h : (p ∧ c) ∨ (q ∧ c) ∨ r) :
-- imply
  (p ∨ q) ∧ c ∨ r := by
-- proof
  rw [Or_Or.is.OrOr] at h
  simp only [OrAndS.is.AndOr] at h
  assumption


-- created on 2025-04-07
-- updated on 2025-04-08
