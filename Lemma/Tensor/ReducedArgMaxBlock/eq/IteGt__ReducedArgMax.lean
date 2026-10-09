import sympy.Basic
import sympy.concrete.reduced


@[path]
private lemma main
  {m n : ℕ} [NeZero m] [NeZero n]
  {x : Fin m → ℝ}
  {y : Fin n → ℝ}
-- given
  (hx : ∀ i, 0 ≤ x i) :
-- imply
  ReducedArgMax (Fin.append x y) =
    if Function.max y > Function.max x then
      ReducedArgMax (Fin.append (0 : Fin m → ℝ) y)
    else
      ReducedArgMax (Fin.append x (0 : Fin n → ℝ)) := by
-- proof
  have hx_max : 0 ≤ Function.max x := by
    rw [← ReducedArgMax.eq_max x]
    exact hx _
  have hmax0m : Function.max (0 : Fin m → ℝ) = 0 := by
    rw [← ReducedArgMax.eq_max (0 : Fin m → ℝ)]
    simp
  have hmax0n : Function.max (0 : Fin n → ℝ) = 0 := by
    rw [← ReducedArgMax.eq_max (0 : Fin n → ℝ)]
    simp
  rw [ReducedArgMax.append_eq_ite]
  if hgt : Function.max y > Function.max x then
    have hz1 : ReducedArgMax (Fin.append (0 : Fin m → ℝ) y) = Fin.natAdd m (ReducedArgMax y) := by
      rw [ReducedArgMax.append_eq_ite, hmax0m, ite_eq_left (lt_of_le_of_lt hx_max hgt)]
    rw [ite_eq_left hgt, ite_eq_left hgt, hz1]
  else
    have hz2 : ReducedArgMax (Fin.append x (0 : Fin n → ℝ)) = Fin.castAdd n (ReducedArgMax x) := by
      rw [ReducedArgMax.append_eq_ite, hmax0n, ite_eq_right (not_lt.mpr hx_max)]
    rw [ite_eq_right hgt, ite_eq_right hgt, hz2]


-- created on 2026-10-09
