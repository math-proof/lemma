/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Probability/McDiarmid.lean -/


import Lemma.Measure.McDiarmid
open MathlibExt.Probability.McDiarmid


/-- One fair coin and its indicator: sensitivity `1` gives the tail bound `exp (-2 t ^ 2)`. -/
example (t : ℝ) (ht : 0 < t) :
    ∑ _x ∈ (Finset.univ.filter fun x : Fin 1 → Bool => decide
        (t ≤ (if x 0 then 1 else 0) -
          ∑ y : Fin 1 → Bool, (∏ _i : Fin 1, (1 / 2 : ℝ)) * (if y 0 then 1 else 0))),
      ∏ _i : Fin 1, (1 / 2 : ℝ) ≤ Real.exp (-2 * t ^ 2 / ∑ _i : Fin 1, (1 : ℝ) ^ 2) :=
  mcdiarmid_one_sided_finite_iid_general (α := Bool) (n := 1) (fun _ => 1 / 2)
    (fun _ => by norm_num) (by norm_num) (fun x => if x 0 then 1 else 0) (fun _ => 1)
    (fun _ => zero_le_one) (by norm_num) t ht (fun _ x y _ => by split_ifs <;> norm_num)

/-- With `n = 0` the sensitivity sum is `0` and the upper tail is empty for any `f`. -/
example {α : Type*} [Fintype α] [Nonempty α] (p : α → ℝ) (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : α, p a = 1) (f : (Fin 0 → α) → ℝ) (t : ℝ) (ht : 0 < t) :
    ∑ x ∈ (Finset.univ.filter fun x => decide
        (t ≤ f x - ∑ y : Fin 0 → α, (∏ i : Fin 0, p (y i)) * f y)),
      ∏ i : Fin 0, p (x i) = 0 :=
  mcdiarmid_one_sided_finite_iid_of_sum_sq_eq_zero p hp_nonneg hp_sum f (fun _ => 0)
    (fun _ => le_rfl) (by simp) t ht (fun i => i.elim0)

/-- The general bound elaborates without `[DecidableEq α]`. -/
example {α : Type*} [Fintype α] [Nonempty α] {n : ℕ} (p : α → ℝ) (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : α, p a = 1) (f : (Fin n → α) → ℝ) (c : Fin n → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i) (hc_pos : 0 < ∑ i : Fin n, c i ^ 2) (t : ℝ) (ht : 0 < t)
    (hbd : ∀ (i : Fin n) (x y : Fin n → α), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    ∑ x ∈ (Finset.univ.filter fun x => decide
        (t ≤ f x - ∑ y : Fin n → α, (∏ i : Fin n, p (y i)) * f y)),
      ∏ i : Fin n, p (x i) ≤ Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) :=
  mcdiarmid_one_sided_finite_iid_general p hp_nonneg hp_sum f c hc_nonneg hc_pos t ht hbd

