import Mathlib
import sympy.Basic
open scoped TensorProduct


/--
[Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [HenselianLocalRing R]
  {E : Type v} [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
  {B : Type w} [CommRing B] [Algebra R B] [Module.Finite R B]
  {φ ψ : E →ₐ[R] B}
-- given
  (h : ∀ x : E, φ x - ψ x ∈ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) :
-- imply
  φ = ψ := by
-- proof
  classical
    set I : Ideal B := Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) with hI
    have hIJ : I ≤ Ideal.jacobson (⊥ : Ideal B) := by
      refine le_sInf fun J hJ => ?_
      obtain ⟨-, hJmax⟩ := hJ
      rw [hI, Ideal.map_le_iff_le_comap]
      have := hJmax
      have hc : (J.comap (algebraMap R B)).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R B) (fun b => IsIntegral.of_finite R b) J
      rw [← IsLocalRing.eq_maximalIdeal hc]
    set e : E ⊗[R] E := Algebra.FormallyUnramified.elem R E with he
    have he1 : ∀ s : E, ((1 : E) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : E)) * e = 0 :=
      fun s => Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem s
    have he2 : Algebra.TensorProduct.lmul' R e = 1 := Algebra.FormallyUnramified.lmul_elem
    set Φ : E ⊗[R] E →ₐ[R] B := Algebra.TensorProduct.productMap φ ψ with hΦ
    have hΦμ : ∀ t : E ⊗[R] E, Φ t - φ (Algebra.TensorProduct.lmul' R t) ∈ I := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
          rw [hΦ, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul,
            ← mul_sub]
          refine I.mul_mem_left _ ?_
          have := I.neg_mem (h b)
          rwa [neg_sub] at this
      | add u v hu hv =>
          rw [map_add, map_add, map_add]
          convert I.add_mem hu hv using 1
          ring
    have hΦe : Φ e - 1 ∈ Ideal.jacobson (⊥ : Ideal B) := by
      apply hIJ
      simpa [he2] using hΦμ e
    have hunit : IsUnit (Φ e) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ hΦe
    refine AlgHom.ext fun x => ?_
    have hdx : Φ (x ⊗ₜ[R] 1 - 1 ⊗ₜ[R] x) = φ x - ψ x := by
      rw [map_sub, hΦ, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
        map_one, map_one, mul_one, one_mul]
    have hann : (x ⊗ₜ[R] (1 : E) - (1 : E) ⊗ₜ[R] x) * e = 0 := by
      rw [← neg_sub, neg_mul, he1 x, neg_zero]
    apply sub_eq_zero.mp
    apply hunit.mul_left_eq_zero.mp
    rw [← hdx, ← map_mul, hann, map_zero]


-- created on 2026-10-10
