import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


/--
[ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly.lean)
-/
@[path]
private lemma main
  [Field F] [Field L] [Algebra F L]
  {𝒪 : ValuationSubring F} [Algebra 𝒪 L] [IsScalarTower 𝒪 F L]
  {c z : L}
-- given
  (hc : IsIntegral 𝒪 c)
  (hgen : IntermediateField.adjoin F ({c} : Set L) = ⊤)
  (hdisc : ∃ u : 𝒪ˣ, algebraMap 𝒪 F u = Algebra.norm F (aeval c (derivative (minpoly F c))))
  (hz : IsIntegral 𝒪 z) :
-- imply
  z ∈ Algebra.adjoin 𝒪 ({c} : Set L) := by
-- proof
  classical
    have hcF : IsIntegral F c := hc.tower_top
    let e : IntermediateField.adjoin F ({c} : Set L) ≃ₐ[F] L :=
      (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
    let pb : PowerBasis F L := (IntermediateField.adjoin.powerBasis hcF).map e
    have hpb : pb.gen = c := by
      show e (IntermediateField.adjoin.powerBasis hcF).gen = c
      rw [IntermediateField.adjoin.powerBasis_gen]
      rfl
    have : FiniteDimensional F L := PowerBasis.finite pb
    obtain ⟨u, hu⟩ := hdisc
    have hN0 : Algebra.norm F (aeval c (derivative (minpoly F c))) ≠ 0 := by
      rw [← hu]
      exact fun h => u.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective 𝒪 F)).mp h)
    have hder : aeval c (derivative (minpoly F c)) ≠ 0 := fun h => hN0 (by rw [h, Algebra.norm_zero])
    have hsc : IsSeparable F c := by
      refine (separable_iff_derivative_ne_zero (minpoly.irreducible hcF)).mpr ?_
      intro h0
      exact hder (by rw [h0, map_zero])
    have : Algebra.IsSeparable F L := by
      have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F L).mpr hsc
      exact AlgEquiv.Algebra.isSeparable e
    have hmem := Algebra.discr_mul_isIntegral_mem_adjoin F (B := pb) (by rwa [hpb]) hz
    rw [hpb] at hmem
    set k : ℕ := Module.finrank F L * (Module.finrank F L - 1) / 2 with hk
    have hd : Algebra.discr F pb.basis = (-1) ^ k * Algebra.norm F (aeval c (derivative (minpoly F c))) := by
      rw [Algebra.discr_powerBasis_eq_norm, hpb]
    have key : z = ((-1 : L) ^ k * algebraMap 𝒪 L ↑u⁻¹) * (Algebra.discr F pb.basis • z) := by
      rw [Algebra.smul_def, hd, map_mul, map_pow, map_neg, map_one, ← hu, ← IsScalarTower.algebraMap_apply 𝒪 F L]
      have h1 : ((-1 : L) ^ k) * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      have h2 : algebraMap 𝒪 L ↑u⁻¹ * algebraMap 𝒪 L ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      symm
      calc
        _ = ((-1 : L) ^ k * (-1) ^ k) * (algebraMap 𝒪 L ↑u⁻¹ * algebraMap 𝒪 L ↑u) * z := by ring
        _ = z := by rw [h1, h2, one_mul, one_mul]
    rw [key]
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ (Subalgebra.algebraMap_mem _ _)) hmem
    exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _


-- created on 2026-10-23
