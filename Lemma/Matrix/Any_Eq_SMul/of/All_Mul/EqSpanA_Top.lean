import Mathlib
import sympy.Basic


/--
[Matrix_exists_eq_smul_one_of_commute_of_span_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_exists_eq_smul_one_of_commute_of_span_eq_top.lean)
-/
@[main]
private lemma main
  [Fintype n] [DecidableEq n] [CommRing A]
  {S : Set (Matrix n n A)}
  {M : Matrix n n A}
-- given
  (hS : Submodule.span A S = ⊤)
  (hM : ∀ X ∈ S, X * M = M * X) :
-- imply
  ∃ a : A, M = a • 1 := by
-- proof
  have hcomm : ∀ X : Matrix n n A, X * M = M * X := by
    have hle : Submodule.span A S ≤
        { carrier := {X | X * M = M * X}
          add_mem' := fun {X} {Y} hX hY => by
            simp only [Set.mem_ofPred_eq] at hX hY ⊢
            rw [add_mul, mul_add, hX, hY]
          zero_mem' := by simp
          smul_mem' := fun a X hX => by
            simp only [Set.mem_ofPred_eq] at hX ⊢
            rw [smul_mul_assoc, mul_smul_comm, hX] } :=
      Submodule.span_le.mpr hM
    intro X
    exact hle (hS ▸ Submodule.mem_top)
  have hMc : M ∈ Set.center (Matrix n n A) := Semigroup.mem_center_iff.mpr hcomm
  rw [Matrix.center_eq_range] at hMc
  obtain ⟨a, ha⟩ := hMc
  refine ⟨a, ?_⟩
  rw [← ha, Matrix.scalar_apply]
  ext i j
  simp [Matrix.one_apply, Matrix.diagonal_apply, Matrix.smul_apply]


-- created on 2026-10-05
