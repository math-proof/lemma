import sympy.Basic
import sympy.concrete.expr_with_limits
import sympy.concrete.reduced


@[main]
private lemma main
  {m n : ℕ} [NeZero m] [NeZero n]
  {x : Fin m → ℝ}
  {y : Fin n → ℝ} :
-- imply
  ReducedArgMax (Fin.append x y) =
    if Function.max y > Function.max x then Fin.natAdd m (ReducedArgMax y)
    else Fin.castAdd n (ReducedArgMax x) := by
-- proof
  have hx_le : ∀ i, x i ≤ Function.max x :=
    fun i => Finset.le_sup' x (Finset.mem_univ i)
  have hy_le : ∀ j, y j ≤ Function.max y :=
    fun j => Finset.le_sup' y (Finset.mem_univ j)
  have hrx_eq : x (ReducedArgMax x) = Function.max x := ReducedArgMax.eq_max x
  have hry_eq : y (ReducedArgMax y) = Function.max y := ReducedArgMax.eq_max y
  if hgt : Function.max y > Function.max x then
    have hry_le : ∀ j, y j ≤ y (ReducedArgMax y) := fun j => by rw [hry_eq]; exact hy_le j
    have hc_val : (Fin.append x y) (Fin.natAdd m (ReducedArgMax y)) = y (ReducedArgMax y) := by
      simp only [Fin.append_right]
    have hc_max : ∀ j, (Fin.append x y) j ≤ y (ReducedArgMax y) := by
      intro j
      induction j using Fin.addCases with
      | left i =>
        simp only [Fin.append_left]
        rw [hry_eq]
        exact ((hx_le i).trans_lt hgt).le
      | right j =>
        simp only [Fin.append_right]
        exact hry_le j
    have hc_max' : ∀ j,
        (Fin.append x y) j ≤ (Fin.append x y) (Fin.natAdd m (ReducedArgMax y)) := by
      intro j
      rw [hc_val]
      exact hc_max j
    have hc_first : ∀ i,
        (∀ k, (Fin.append x y) k ≤ (Fin.append x y) i) →
        (Fin.natAdd m (ReducedArgMax y) : Fin (m + n)) ≤ i := by
      intro i hi
      induction i using Fin.addCases with
      | left i' =>
        simp only [Fin.append_left] at hi
        exact (by linarith [hry_eq, hx_le i', hgt, hc_val ▸ hi (Fin.natAdd m (ReducedArgMax y))] : False).elim
      | right j' =>
        simp only [Fin.append_right] at hi
        have hj'_le : y j' ≤ y (ReducedArgMax y) := hry_le j'
        have hi_j' : y (ReducedArgMax y) ≤ y j' := by
          rw [← hc_val]
          exact hi (Fin.natAdd m (ReducedArgMax y))
        have hj'_eq : y j' = y (ReducedArgMax y) := le_antisymm hj'_le hi_j'
        have hj'_max : ∀ k, y k ≤ y j' := by
          intro k
          rw [hj'_eq]
          exact hry_le k
        apply (Fin.strictMono_natAdd m).le_iff_le.mpr
        exact ReducedArgMax.le_of_forall_le y hj'_max
    rw [ite_eq_left hgt]
    refine le_antisymm ?_ ?_
    · exact ReducedArgMax.le_of_forall_le _ hc_max'
    · exact hc_first _ (ReducedArgMax.le _)
  else
    have hle : Function.max y ≤ Function.max x := not_lt.mp hgt
    have hrx_le : ∀ i, x i ≤ x (ReducedArgMax x) := fun i => by rw [hrx_eq]; exact hx_le i
    have hry_le : ∀ j, y j ≤ y (ReducedArgMax y) := fun j => by rw [hry_eq]; exact hy_le j
    have hc_val : (Fin.append x y) (Fin.castAdd n (ReducedArgMax x)) = x (ReducedArgMax x) := by
      simp only [Fin.append_left]
    have hc_max : ∀ j, (Fin.append x y) j ≤ x (ReducedArgMax x) := by
      intro j
      induction j using Fin.addCases with
      | left i =>
        simp only [Fin.append_left]
        exact hrx_le i
      | right j =>
        simp only [Fin.append_right]
        exact (hy_le j).trans (hle.trans hrx_eq.symm.le)
    have hc_max' : ∀ j,
        (Fin.append x y) j ≤ (Fin.append x y) (Fin.castAdd n (ReducedArgMax x)) := by
      intro j
      rw [hc_val]
      exact hc_max j
    have hc_first : ∀ i,
        (∀ k, (Fin.append x y) k ≤ (Fin.append x y) i) →
        (Fin.castAdd n (ReducedArgMax x) : Fin (m + n)) ≤ i := by
      intro i hi
      induction i using Fin.addCases with
      | left i' =>
        simp only [Fin.append_left] at hi
        have hxi'_max : ∀ k, x k ≤ x i' := by
          intro k
          have := hi (Fin.castAdd n k)
          rwa [Fin.append_left] at this
        apply (Fin.strictMono_castAdd n).le_iff_le.mpr
        exact ReducedArgMax.le_of_forall_le x hxi'_max
      | right j' =>
        simp only [Fin.append_right] at hi
        show (ReducedArgMax x).val ≤ m + j'.val
        exact (ReducedArgMax x).isLt.le.trans (Nat.le_add_right _ _)
    rw [ite_eq_right hgt]
    refine le_antisymm ?_ ?_
    · exact ReducedArgMax.le_of_forall_le _ hc_max'
    · exact hc_first _ (ReducedArgMax.le _)


-- created on 2026-10-09
