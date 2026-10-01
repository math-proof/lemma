import sympy.Basic


@[main]
private lemma upper_triangle
  {n u : ℕ}
  (A : Fin n → Fin n → ℝ) :
-- imply
  ∀ (i : Fin n) (c : Fin u), (if h : i.val + c.val < n then ((A i ⟨i.val + c.val, h⟩ : ℝ) : EReal) else ⊥) ≤ ((Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val < i.val + u), Real.exp (A i k)) : ℝ) : EReal) := by
-- proof
  have key : ∀ (i j : Fin n) (P : Fin n → Prop) [DecidablePred P], P j → A i j ≤ Real.log (∑ k ∈ Finset.univ.filter P, Real.exp (A i k)) := by
    intro i j P _ hp
    calc A i j = Real.log (Real.exp (A i j)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (Finset.single_le_sum (f := fun k => Real.exp (A i k)) (fun k _ => (Real.exp_pos _).le) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩))
  intro i c
  split_ifs with h
  ·
    exact EReal.coe_le_coe_iff.mpr (key i _ _ ⟨Nat.le_add_right _ _, by have := c.isLt; simp only; omega⟩)
  ·
    exact bot_le


@[main]
private lemma lower_triangle
  {n l : ℕ}
  (A : Fin n → Fin n → ℝ) :
-- imply
  ∀ (i : Fin n) (c : Fin l), (if h : l - 1 ≤ i.val + c.val then ((A i ⟨i.val + c.val - (l - 1), by have := c.isLt; have := i.isLt; omega⟩ : ℝ) : EReal) else ⊥) ≤ ((Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val + l ∧ k.val ≤ i.val), Real.exp (A i k)) : ℝ) : EReal) := by
-- proof
  have key : ∀ (i j : Fin n) (P : Fin n → Prop) [DecidablePred P], P j → A i j ≤ Real.log (∑ k ∈ Finset.univ.filter P, Real.exp (A i k)) := by
    intro i j P _ hp
    calc A i j = Real.log (Real.exp (A i j)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (Finset.single_le_sum (f := fun k => Real.exp (A i k)) (fun k _ => (Real.exp_pos _).le) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩))
  intro i c
  split_ifs with h
  ·
    exact EReal.coe_le_coe_iff.mpr (key i _ _ ⟨by have := c.isLt; simp only; omega, by have := c.isLt; simp only; omega⟩)
  ·
    exact bot_le


-- created on 2022-03-31
