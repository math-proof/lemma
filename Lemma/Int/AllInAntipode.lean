import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

/--
[HopfOrder_antipode_mem_sup](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfOrder_antipode_mem_sup.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {K : Type v} [Field K] [Algebra R K]
  {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
  {S S' : Subalgebra R A}
  (hS : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S)
  (hS' : ∀ x ∈ S', HopfAlgebra.antipode K x ∈ S') :
  -- imply
  ∀ x ∈ S ⊔ S', HopfAlgebra.antipode K x ∈ S ⊔ S' := by
  -- proof
  let T : Subalgebra R A :=
    { carrier := {x | HopfAlgebra.antipode K x ∈ S ⊔ S'}
      mul_mem' := by
        intro a b ha hb
        change HopfAlgebra.antipode K (a * b) ∈ S ⊔ S'
        rw [HopfAlgebra.antipode_mul_antidistrib]
        apply Subalgebra.mul_mem _ hb ha
      one_mem' := by
        change HopfAlgebra.antipode K (1 : A) ∈ S ⊔ S'
        rw [HopfAlgebra.antipode_one]
        apply Subalgebra.one_mem _
      add_mem' := by
        intro a b ha hb
        change HopfAlgebra.antipode K (a + b) ∈ S ⊔ S'
        rw [map_add]
        apply Subalgebra.add_mem _ ha hb
      zero_mem' := by
        change HopfAlgebra.antipode K (0 : A) ∈ S ⊔ S'
        rw [map_zero]
        apply Subalgebra.zero_mem _
      algebraMap_mem' := by
        intro r
        change HopfAlgebra.antipode K (algebraMap R A r) ∈ S ⊔ S'
        have h1 : algebraMap R A r = algebraMap R K r • (1 : A) := by
          rw [IsScalarTower.algebraMap_apply R K A, Algebra.algebraMap_eq_smul_one]
        rw [h1, map_smul, HopfAlgebra.antipode_one, ← h1]
        apply Subalgebra.algebraMap_mem _ r }
  have key : S ⊔ S' ≤ T := sup_le (fun y hy => (le_sup_left : S ≤ S ⊔ S') (hS y hy))
    (fun y hy => (le_sup_right : S' ≤ S ⊔ S') (hS' y hy))
  intro x hx
  apply key hx


-- created on 2026-10-20
