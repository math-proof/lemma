import sympy.tensor.stack_ite
import sympy.Basic


@[path]
private lemma main
-- given
  (m : ℕ)
  (s : Fin (m + 1) → ℕ)
  (f : Fin (m + 1) → ℕ → α)
  (j : Fin (m + 1))
  (k : ℕ)
  (hk : k < s j) :
-- imply
  Tensor.stackIte m s f (∑ i : Fin j, s (Fin.castLE j.2.le i) + k) = f j k := by
-- proof
  induction m with
  | zero =>
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    simp [Tensor.stackIte]
  | succ m ih =>
    refine Fin.cases ?_ (fun j' hk => ?_) j hk
    ·
      intro hk
      have h0 : ∑ i : Fin ((0 : Fin (m + 2)) : ℕ), s (Fin.castLE (0 : Fin (m + 2)).2.le i) = 0 :=
        Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
      rw [h0, zero_add, Tensor.stackIte, if_pos hk]
    ·
      have hsum : ∑ i : Fin (j'.succ : ℕ), s (Fin.castLE j'.succ.2.le i) =
          s 0 + ∑ i : Fin j', Fin.tail s (Fin.castLE j'.2.le i) := by
        change ∑ i : Fin ((j' : ℕ) + 1), s (Fin.castLE j'.succ.2.le i) = _
        rw [Fin.sum_univ_succ]
        rfl
      rw [hsum, Tensor.stackIte, if_neg (by omega), show s 0 + ∑ i : Fin j', Fin.tail s (Fin.castLE j'.2.le i) + k - s 0 =
        ∑ i : Fin j', Fin.tail s (Fin.castLE j'.2.le i) + k by omega]
      exact ih (Fin.tail s) (Fin.tail f) j' hk


-- created on 2026-10-07
