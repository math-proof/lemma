import Initialize.Tactic.Attr.Basic
import Mathlib


/-- Split a sum over two halves: \(\sum_i f_i = \sum_t f(t) + \sum_t f(t + d)\). -/
@[path]
private lemma main
  {d : ℕ}
-- given
  (f : Fin (d + d) → ℝ) :
-- imply
  ∑ i, f i = ∑ t : Fin d, f (t.castAdd d) + ∑ t : Fin d, f (t.natAdd d) := by
-- proof
  let e := finSumFinEquiv (m := d) (n := d)
  have hs : ∑ i, f i = ∑ s : Fin d ⊕ Fin d, f (e s) := (e.sum_comp f).symm
  rw [hs, Fintype.sum_sum_type]
  refine congrArg₂ HAdd.hAdd ?_ ?_
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [e, finSumFinEquiv_apply_left]
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [e, finSumFinEquiv_apply_right]


-- created on 2026-11-27
