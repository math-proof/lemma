import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {f : ℝ}
-- given
  (h : f * (if p then 1 else 0) ≥ 1) :
-- imply
  f ≥ 1 ∧ p := by
-- proof
  if hp : p then
    rw [ite_eq_left hp, mul_one] at h
    exact ⟨h, hp⟩
  else
    rw [ite_eq_right hp, mul_zero] at h
    exact absurd h (by norm_num)


-- created on 2023-11-05
