import Lemma.Bool.And_Or.is.OrAndS
import Lemma.Logic.AndAnd_Not.is.False
import Lemma.Bool.AndAndNot.is.False
import Lemma.Logic.NotAnd.is.OrNotS
open Logic Bool


@[main, comm, mp, mpr]
private lemma Main :
-- imply
  ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
-- proof
  constructor <;>
    intro h <;>
    by_contra h'
  ·
    rw [NotAnd.is.OrNotS] at h'
    simp at h'
    contradiction
  ·
    have h := OrAndS.of.And_Or h h'
    simp [AndAnd_Not.is.False, AndAndNot.is.False] at h


-- created on 2024-07-01
-- updated on 2025-07-30
