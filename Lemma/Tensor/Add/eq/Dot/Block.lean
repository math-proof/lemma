import sympy.Basic


@[main]
private lemma main
  [Semiring α]
  {k t : ℕ}
  {ξ : ℕ → α}
  {L : ℕ → ℕ → α}
-- given
  (h : k < t) :
-- imply
  (fun c => ∑ r ∈ Finset.Ico (k + 1) t, ξ r * L r c + L t c) = fun c => ∑ r ∈ Finset.Ico (k + 1) (t + 1), (if r = t then 1 else ξ r) * L r c := by
-- proof
  funext c
  rw [Finset.sum_Ico_succ_top (Nat.succ_le_of_lt h), if_pos rfl, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [if_neg (Finset.mem_Ico.mp hr).2.ne]


-- created on 2023-06-27
