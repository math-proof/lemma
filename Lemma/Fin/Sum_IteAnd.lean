import Initialize.Tactic.Attr.Basic
import Instance.Data.Fin.Fun
import Mathlib


/-- Commuting the conjunction inside `sum`-over-`Fin` with a conditional term. -/
@[path, Fun]
private lemma main
  [AddCommMonoid α]
  {d : ℕ}
  {p q : Fin d → Prop} [DecidablePred p] [DecidablePred q]
-- given
  (f : Fin d → α) :
-- imply
  (∑ t : Fin d, if p[t] ∧ q[t] then f[t] else 0) =
    ∑ t : Fin d, if q[t] ∧ p[t] then f[t] else 0 := by
-- proof
  refine Finset.sum_congr rfl fun t _ => ?_
  if h : p[t] ∧ q[t] then
    rw [ite_eq_left h, ite_eq_left h.symm]
  else
    have h' : ¬ (q[t] ∧ p[t]) := fun hc => h hc.symm
    rw [ite_eq_right h, ite_eq_right h']


-- created on 2026-11-26
-- updated on 2026-11-27
