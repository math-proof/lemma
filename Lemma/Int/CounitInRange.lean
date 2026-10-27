import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

/--
[HopfOrder_counit_mem_range_sup](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfOrder_counit_mem_range_sup.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {K : Type v} [Field K] [Algebra R K]
  {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
  {S S' : Subalgebra R A}
  (hS : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
  (hS' : ∀ x ∈ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
  -- imply
  ∀ x ∈ S ⊔ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range := by
  -- proof
  have key : S ⊔ S' ≤ Subalgebra.comap ((Bialgebra.counitAlgHom K A).restrictScalars R) (⊥ : Subalgebra R K) := by
    rw [sup_le_iff]
    constructor
    ·
      intro y hy
      rw [Subalgebra.mem_comap, Algebra.mem_bot]
      apply hS y hy
    ·
      intro y hy
      rw [Subalgebra.mem_comap, Algebra.mem_bot]
      apply hS' y hy
  intro x hx
  have hmem := key hx
  rw [Subalgebra.mem_comap, Algebra.mem_bot] at hmem
  apply hmem


-- created on 2026-10-20
