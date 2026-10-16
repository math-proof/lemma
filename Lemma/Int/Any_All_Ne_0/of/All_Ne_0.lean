import Mathlib
import sympy.Basic


/--
[Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  [Field k] [IsAlgClosed k]
  [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
  {ι : Type u} [Finite ι]
  {g : ι → B}
-- given
  (hg : ∀ i, g i ≠ 0) :
-- imply
  ∃ χ : B →ₐ[k] k, ∀ i, χ (g i) ≠ 0 := by
-- proof
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  set G : B := ∏ i, g i with hGdef
  have hG : G ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hg i)
  let S := Localization.Away G
  let _ : Nontrivial S := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    apply absurd (IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hG) (show algebraMap B S 0 = algebraMap B S 1 by rw [map_zero, map_one]; apply h)) zero_ne_one
  let _ : Algebra.FiniteType k S := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  let _ : Ideal.IsMaximal m := hm
  let _ : Field (S ⧸ m) := Ideal.Quotient.field m
  let _ : Algebra.FiniteType k (S ⧸ m) := Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  let _ : Module.Finite k (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
  let _ : Algebra.IsAlgebraic k (S ⧸ m) := Algebra.IsAlgebraic.of_finite k (S ⧸ m)
  let φ : (S ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  let ψ : B →ₐ[k] S ⧸ m := (Ideal.Quotient.mkₐ k m).comp (IsScalarTower.toAlgHom k B S)
  refine ⟨φ.comp ψ, fun i => ?_⟩
  have hGunit : IsUnit (algebraMap B S G) := IsLocalization.Away.algebraMap_isUnit G
  have hGS : (φ.comp ψ) G ≠ 0 := by
    intro h0
    apply (IsUnit.ne_zero · h0)
    rw [show (φ.comp ψ) G = φ (Ideal.Quotient.mk m (algebraMap B S G)) from rfl]
    apply (hGunit.map (Ideal.Quotient.mk m)).map φ
  intro hgi
  apply hGS
  show (φ.comp ψ) (∏ i, g i) = 0
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i) hgi


-- created on 2026-10-13
