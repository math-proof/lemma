import Mathlib
import sympy.Basic


/--
[exists_mem_addSubgroup_one_add_mul_one_add_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_exists_mem_addSubgroup_one_add_mul_one_add_eq_one.lean)
-/
@[path]
private lemma main
  [NormedField L] [CompleteSpace L]
  {M : AddSubgroup L}
  {x : L}
-- given
  (hMclosed : IsClosed (M : Set L))
  (hMmul : ∀ x y : L, x ∈ M → y ∈ M → x * y ∈ M)
  (hMnorm : ∀ x ∈ M, ‖x‖ < 1)
  (hx : x ∈ M) :
-- imply
  ∃ y ∈ M, (1 + x) * (1 + y) = 1 := by
-- proof
  have hx1 : ‖-x‖ < 1 := by rw [norm_neg]; exact hMnorm x hx

  have hS : HasSum (fun n : ℕ => (-x) ^ n) (1 - -x)⁻¹ := hasSum_geometric_of_norm_lt_one hx1
  have hS' : HasSum (fun n : ℕ => (-x) ^ (n + 1)) ((1 - -x)⁻¹ - 1) := by
    have h := (hasSum_nat_add_iff' 1).2 hS
    simpa only [Finset.sum_range_one, pow_zero] using h

  have hpow : ∀ n : ℕ, (-x) ^ (n + 1) ∈ M := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one]; exact M.neg_mem hx
    | succ n ih => rw [pow_succ]; exact hMmul _ _ ih (M.neg_mem hx)

  have hyM : (1 - -x)⁻¹ - 1 ∈ M :=
    hMclosed.mem_of_tendsto hS'.tendsto_sum_nat
      (Filter.Eventually.of_forall fun N => M.sum_mem fun i _ => hpow i)
  have hne : (1 + x : L) ≠ 0 := by
    intro h
    have hx' : x = -1 := by linear_combination h
    have h1 := hMnorm x hx
    rw [hx', norm_neg, norm_one] at h1
    exact lt_irrefl _ h1
  refine ⟨(1 - -x)⁻¹ - 1, hyM, ?_⟩
  have e : (1 : L) + ((1 - -x)⁻¹ - 1) = (1 + x)⁻¹ := by ring
  rw [e, mul_inv_cancel₀ hne]


-- created on 2026-10-05
