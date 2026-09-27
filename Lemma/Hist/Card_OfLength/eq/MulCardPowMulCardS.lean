import sympy.stats.mdp_history
import sympy.Basic


@[main]
private lemma main
  {S : Type*} {A : Type*} [Fintype S] [Fintype A]
-- given
  (t : ℕ) :
-- imply
  Fintype.card (Hist.OfLength S A t) = Fintype.card S * (Fintype.card A * Fintype.card S) ^ t := by
-- proof
  induction t with
  | zero =>
    rw [Fintype.card_congr Hist.ofLengthZeroEquiv, pow_zero, mul_one]
  | succ t ih =>
    rw [Fintype.card_congr (Hist.ofLengthSuccEquiv t), Fintype.card_prod, Fintype.card_prod, ih, pow_succ]
    ring


-- created on 2026-09-26
