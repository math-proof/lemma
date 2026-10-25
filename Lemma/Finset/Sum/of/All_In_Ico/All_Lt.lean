import Theorem.Algebra.BigOperators.Reduced.Part2
import sympy.Basic


/--
py `Finset.Sum.of.All_In_Ico.All_Lt`:
masked sum \(\sum_{d_j < i} f(i,j)\) equals the leading slice through
\(\operatorname{ReducedArgMax}(d - i - n\cdot\mathbf{1}_{d\ge i})\).
-/
@[path]
private lemma main
  {n m : ℕ} [NeZero m]
  {d : Fin m → ℤ}
  {f : ℕ → Fin m → ℝ}
  {i : ℕ}
-- given
  (h_lt : ∀ (i j : Fin m), j < i → d j < d i)
  (h_subset : ∀ j : Fin m, d j ∈ Set.Ico (0 : ℤ) (n : ℤ))
  (h_nonempty : ∃ j : Fin m, d j < (i : ℤ)) :
-- imply
  let v := fun k : Fin m =>
    (d k : ℝ) - (i : ℝ) - (n : ℝ) * (if (d k : ℤ) ≥ (i : ℤ) then (1 : ℝ) else 0)
  (∑ j ∈ Finset.univ.filter (fun j : Fin m => d j < (i : ℤ)), f i j) =
    ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val ≤ (ReducedArgMax v).val), f i j := by
-- proof
  intro v
  let M := ReducedArgMax v
  have h_mono {a b : Fin m} (hab : a < b) : d a < d b := h_lt b a hab
  have h_bound (k : Fin m) : (0 : ℤ) ≤ d k ∧ d k < (n : ℤ) :=
    Set.mem_Ico.mp (h_subset k)
  have h_v_lt {k : Fin m} (hk : d k < (i : ℤ)) :
    v k = (d k : ℝ) - (i : ℝ) := by
    simp only [v, ite_eq_right (not_le.mpr hk), mul_zero, sub_zero]
  have h_v_ge {k : Fin m} (hk : d k ≥ (i : ℤ)) :
    v k = (d k : ℝ) - (i : ℝ) - (n : ℝ) := by
    simp only [v, ite_eq_left hk, mul_one]
  have h_sep {k l : Fin m} (hk : d k < (i : ℤ)) (hl : d l ≥ (i : ℤ)) :
    v l < v k := by
    rw [h_v_lt hk, h_v_ge hl]
    have hl1 : (d l : ℝ) ≤ (n : ℝ) - 1 := by
      have := Int.le_sub_one_of_lt (h_bound l).2
      exact_mod_cast this
    have hk0 : (0 : ℝ) ≤ (d k : ℝ) := by
      exact_mod_cast (h_bound k).1
    linarith
  have h_v_mono {k l : Fin m} (hk : d k < (i : ℤ)) (hl : d l < (i : ℤ))
    (hkl : k < l) : v k < v l := by
    rw [h_v_lt hk, h_v_lt hl]
    have : (d k : ℝ) < (d l : ℝ) := by
      exact_mod_cast h_mono hkl
    linarith
  have hM_lt : d M < (i : ℤ) := by
    obtain ⟨k, hk⟩ := h_nonempty
    by_contra hM
    push Not at hM
    have : v k ≤ v M := ReducedArgMax.le v k
    exact (not_le_of_gt (h_sep hk hM)) this
  have hM_max {j : Fin m} (hj : d j < (i : ℤ)) : j ≤ M := by
    by_contra hMj
    push Not at hMj
    have : v M < v j := h_v_mono hM_lt hj hMj
    have : v j ≤ v M := ReducedArgMax.le v j
    linarith
  apply Finset.sum_congr
  ·
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    ·
      intro hj
      exact Fin.le_def.mp (hM_max hj)
    ·
      intro hjM
      have hj_le_M : j ≤ M := Fin.le_def.mpr hjM
      obtain hlt | heq := lt_or_eq_of_le hj_le_M
      · exact lt_trans (h_mono hlt) hM_lt
      · exact heq ▸ hM_lt
  ·
    intros
    rfl


-- created on 2022-04-30
-- updated on 2026-10-12
