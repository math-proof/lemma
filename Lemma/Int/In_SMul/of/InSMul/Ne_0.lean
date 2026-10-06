import Mathlib
import sympy.Basic


/--
[Submodule_mem_ideal_smul_top_of_smul_mem_of_free_of_noZeroSMulDivisors_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_mem_ideal_smul_top_of_smul_mem_of_free_of_noZeroSMulDivisors_quotient.lean)
-/
@[main]
private lemma main
  [CommRing 𝒪] [CommRing R] [Algebra 𝒪 R] [AddCommGroup M] [Module R M] [Module 𝒪 M] [IsScalarTower 𝒪 R M] [Module.Free R M]
  {I : Ideal R} [NoZeroSMulDivisors 𝒪 (R ⧸ I)]
  {a : 𝒪}
  {m : M}
-- given
  (ha : a ≠ 0)
  (h : a • m ∈ (I • ⊤ : Submodule R M)) :
-- imply
  m ∈ (I • ⊤ : Submodule R M) := by
-- proof
  classical
  let b := Module.Free.chooseBasis R M

  have key : ∀ x : M, x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
    intro x
    constructor
    · intro hx i
      refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun y z hy hz => ?_)
      · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact I.mul_mem_right _ hr
      · rw [map_add, Finsupp.add_apply]
        exact I.add_mem hy hz
    · intro hx
      rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top
  rw [key]
  intro i
  have hi : b.repr (a • m) i ∈ I := (key _).mp h i
  rw [← IsScalarTower.algebraMap_smul R a m, map_smul, Finsupp.smul_apply, smul_eq_mul] at hi

  have h0 : a • (Ideal.Quotient.mk I (b.repr m i)) = 0 := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪 R (R ⧸ I), Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hi
  have := (NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero h0).resolve_left ha
  exact Ideal.Quotient.eq_zero_iff_mem.mp this


-- created on 2026-10-05
