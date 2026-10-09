import sympy.stats.step_size
import sympy.Basic


@[path]
private lemma main
-- given
  (anc : Anchors α)
  (n : ℕ) :
-- imply
  anc.t (n + 1) = Nat.find (anc.exists_le n (anc.t n)) := by
-- proof
  exact rfl


-- created on 2026-10-07
