import Mathlib
import sympy.Basic


private lemma exists_dual_apply_ne_zero
  [Field K] [AddCommGroup V] [Module K V]
  {v : V}
-- given
  (hv : v ≠ 0) :
-- imply
  ∃ μ : V →ₗ[K] K, μ v ≠ 0 := by
-- proof
  by_contra h
  apply hv ((Module.forall_dual_apply_eq_zero_iff K v).mp fun μ => not_not.mp (not_exists.mp h μ))

private lemma eq_zero_of_forall_mem_maximal
  [CommRing A] [IsArtinianRing A] [IsReduced A]
  {x : A}
-- given
  (hx : ∀ I : MaximalSpectrum A, x ∈ I.asIdeal) :
-- imply
  x = 0 := by
-- proof
  have hjac : x ∈ Ideal.jacobson (⊥ : Ideal A) := by
    refine Ideal.mem_sInf.mpr ?_
    rintro J ⟨-, hJ⟩
    apply hx ⟨J, hJ⟩
  rw [IsArtinianRing.jacobson_eq_radical] at hjac
  apply ((mem_nilradical (R := A)).mp hjac).eq_zero


/--
[Algebra_exists_linearMap_apply_mul_eq_zero_imp_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_linearMap_apply_mul_eq_zero_imp_of_isReduced.lean)
-/
@[path]
private lemma main
  [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A] [IsReduced A] :
-- imply
  ∃ l : A →ₗ[K] K, ∀ x : A, (∀ y : A, l (x * y) = 0) → x = 0 := by
-- proof
  classical
  let _ : IsArtinianRing A := IsArtinianRing.of_finite K A
  let _ : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have hμ : ∀ I : MaximalSpectrum A,
      ∃ μ : (A ⧸ I.asIdeal) →ₗ[K] K, μ 1 ≠ 0 := by
    intro I
    let _ : Nontrivial (A ⧸ I.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr I.isMaximal.ne_top
    apply exists_dual_apply_ne_zero one_ne_zero
  choose μ hμ using hμ
  let π : ∀ I : MaximalSpectrum A, A →ₗ[K] A ⧸ I.asIdeal :=
    fun I => (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
  have hπ : ∀ (I : MaximalSpectrum A) (x : A), π I x = Ideal.Quotient.mk I.asIdeal x := fun I x => rfl
  refine ⟨∑ I, (μ I).comp (π I), fun x hx => ?_⟩
  refine eq_zero_of_forall_mem_maximal fun I => ?_
  let _ : I.asIdeal.IsMaximal := I.isMaximal
  by_contra hxI
  set u : A ⧸ I.asIdeal := Ideal.Quotient.mk I.asIdeal x with hu
  have hu0 : u ≠ 0 := fun h => hxI (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let _ : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  apply hμ I
  have hcop : Pairwise (Function.onFun IsCoprime fun J : MaximalSpectrum A => J.asIdeal) :=
    fun J J' hJJ' => MaximalSpectrum.isCoprime_of_ne hJJ'
  obtain ⟨y, hy⟩ := Ideal.pi_quotient_surjective hcop
    (Function.update (0 : ∀ J : MaximalSpectrum A, A ⧸ J.asIdeal) I (u⁻¹ * 1))
  have hyI : Ideal.Quotient.mk I.asIdeal y = u⁻¹ * 1 := by
    rw [hy I, Function.update_self]
  have hyJ : ∀ J : MaximalSpectrum A, J ≠ I → Ideal.Quotient.mk J.asIdeal y = 0 := by
    intro J hJ
    rw [hy J, Function.update_of_ne hJ, Pi.zero_apply]
  have hl := hx y
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, hπ, map_mul] at hl
  rw [Finset.sum_eq_single I] at hl
  ·
    rw [hyI, ← hu, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul] at hl
    apply hl
  ·
    intro J _ hJ
    rw [hyJ J hJ, mul_zero, map_zero]
  ·
    intro h
    apply absurd (Finset.mem_univ I) h


-- created on 2026-10-13
