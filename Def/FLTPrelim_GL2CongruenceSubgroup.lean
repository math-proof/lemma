module
public import Mathlib
public import Instance.RepTheory_GL2CongruenceSubgroup
set_option autoImplicit false
open scoped Topology


public section

namespace FLT.SmoothVectors


section CongruenceSubgroup

variable (p : ℕ) [Fact p.Prime]

def gl2CongruenceSubgroup (n : ℕ) : Subgroup (GL (Fin 2) ℚ_[p]) where
  carrier := {g : GL (Fin 2) ℚ_[p] |
    (∀ i j, ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) ∧
    (∀ i j, ‖(((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖
      ≤ (p : ℝ) ^ (-(n : ℤ)))}
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    · simp only [inv_one, Units.val_one, sub_self, Matrix.zero_apply, norm_zero]
      exact le_of_lt (radius_pos p n)
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    refine ⟨hg.2, ?_⟩
    rw [inv_inv]
    exact hg.1
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hh1, hh2⟩ := hh
    have hgentry : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 :=
      norm_entry_le_one_of_sub_entry_le p (radius_le_one p n) hg1
    have hhinventry : ∀ i j,
        ‖((h⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 :=
      norm_entry_le_one_of_sub_entry_le p (radius_le_one p n) hh2
    constructor
    · intro i j
      have hfact : ((g * h : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1
          = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) * ((h : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1)
            + ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) := by
        rw [Units.val_mul, mul_sub, mul_one]
        abel
      rw [hfact, Matrix.add_apply]
      refine padic_norm_add_le_of_le p ?_ (hg1 i j)
      have := norm_matrix_mul_entry_le p hgentry hh1 i j
      rwa [one_mul] at this
    · intro i j
      have hfact : (((g * h)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1
          = ((h⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
              * (((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1)
            + (((h⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) := by
        rw [mul_inv_rev, Units.val_mul, mul_sub, mul_one]
        abel
      rw [hfact, Matrix.add_apply]
      refine padic_norm_add_le_of_le p ?_ (hh2 i j)
      have := norm_matrix_mul_entry_le p hhinventry hg2 i j
      rwa [one_mul] at this

noncomputable def gl2UnipotentPadic (x : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

end CongruenceSubgroup


end FLT.SmoothVectors
