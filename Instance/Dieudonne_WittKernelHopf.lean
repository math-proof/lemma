-- Carved from Lemma/Definitions/Def_Dieudonne_WittKernelHopf.lean: instance decls only.
import Mathlib
import Lemma.Dieudonne.DatumAndHonda
import Instance.Dieudonne_WittVectorHom
import Instance.Dieudonne_WittHomColimit
import Instance.Dieudonne_WittGroupHopf
import Class.HopfAlgebra_HopfIdealQuotient
import Lemma.Dieudonne.WittKernelHopf

set_option autoImplicit false

open Function
open scoped TensorProduct

universe u v w

namespace Deformation


namespace WittKernel

open WittGroup TruncWitt

variable (k : Type u) [CommRing k] (p : ℕ) (n a b : ℕ) (J : Type v)

variable {k p n a b J}

variable [hp : Fact p.Prime]

section HopfIdeal

variable [CharP k p]

variable (k p n a b J)

instance isHopfIdeal : (ideal k p n a b J).IsHopfIdeal' k where
  map_mkₐ_comul_eq_zero := by

    let h : 𝒪 →ₐ[k] (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)).comp
        (Bialgebra.comulAlgHom k 𝒪)
    suffices hle : I ≤ RingHom.ker h.toRingHom by
      intro x hx
      exact hle hx
    rw [ideal_le_iff]
    intro j i
    rw [RingHom.mem_ker]

    set y : TruncatedWittVector p n (𝒪 ⧸ I) := TruncWitt.map (p := p) πI (univ k p n j) with hy
    let iL : (𝒪 ⧸ I) →+* (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
      (Algebra.TensorProduct.includeLeft : (𝒪 ⧸ I) →ₐ[k] _).toRingHom
    let iR : (𝒪 ⧸ I) →+* (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
      (Algebra.TensorProduct.includeRight : (𝒪 ⧸ I) →ₐ[k] _).toRingHom
    have hX : ∀ i, h.toRingHom (X j i) = (TruncWitt.map iL y + TruncWitt.map iR y).coeff i := by
      intro i
      let g : 𝒪 ⊗[k] 𝒪 →+* (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)).toRingHom
      have h1 : h.toRingHom (X j i) = g (WittGroup.comul k p n J (X j i)) := rfl
      rw [h1, ringHom_comul_X]
      congr 2
      · refine TruncatedWittVector.ext fun i => ?_
        rw [TruncatedWittVector.coeff_mk, coeff_map, hy, coeff_map, coeff_univ]
        rfl
      · refine TruncatedWittVector.ext fun i => ?_
        rw [TruncatedWittVector.coeff_mk, coeff_map, hy, coeff_map, coeff_univ]
        rfl
    have hp0 : (p : (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I)) = 0 := natCast_eq_zero_of_algebra k p _
    have hpow : ∀ c : ℕ, h.toRingHom (X j i) ^ p ^ c =
        (TruncWitt.map iL (frobeniusFun^[c] y) + TruncWitt.map iR (frobeniusFun^[c] y)).coeff i := by
      intro c
      rw [hX i, ← coeff_frobeniusFun_iterate, frobeniusFun_iterate_add hp0,
        map_frobeniusFun_iterate, map_frobeniusFun_iterate]
    change h.toRingHom (relation k p n a b J j i) = 0
    rw [relation, map_sub, map_pow, map_pow, hpow, hpow, hy, frobeniusFun_iterate_map_mk_univ,
      sub_self]
  counit_eq_zero := by
    suffices hle : I ≤ RingHom.ker (Bialgebra.counitAlgHom k 𝒪).toRingHom by
      intro x hx
      exact hle hx
    rw [ideal_le_iff]
    intro j i
    rw [RingHom.mem_ker]
    change Coalgebra.counit (R := k) (relation k p n a b J j i) = 0
    rw [relation, counit_def, map_sub, map_pow, map_pow, counit_X,
      zero_pow (pow_ne_zero _ hp.out.ne_zero), zero_pow (pow_ne_zero _ hp.out.ne_zero), sub_self]
  antipode_mem := by
    suffices hle : I ≤ (ideal k p n a b J).comap (WittGroup.antipode k p n J) by
      intro x hx
      have := hle hx
      rwa [Ideal.mem_comap, ← antipode_def] at this
    rw [ideal_le_iff]
    intro j i
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    set g : 𝒪 →+* 𝒪 ⧸ I := (πI).comp (WittGroup.antipode k p n J).toRingHom with hg
    set y : TruncatedWittVector p n (𝒪 ⧸ I) := TruncWitt.map (p := p) πI (univ k p n j) with hy
    have hX : ∀ i, g (X j i) = (-y).coeff i := by
      intro i
      rw [hg, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, antipode_X,
        ← coeff_map (p := p), map_neg, hy]
    have hp0 : (p : 𝒪 ⧸ I) = 0 := natCast_eq_zero_of_algebra k p _
    have hpow : ∀ c : ℕ, g (X j i) ^ p ^ c = (-(frobeniusFun^[c] y)).coeff i := by
      intro c
      rw [hX i, ← coeff_frobeniusFun_iterate, frobeniusFun_iterate_neg hp0]
    change g (relation k p n a b J j i) = 0
    rw [relation, map_sub, map_pow, map_pow, hpow, hpow, hy, frobeniusFun_iterate_map_mk_univ,
      sub_self]

end HopfIdeal

variable (k p n a b J)

variable [CharP k p]

variable {k p n a b J}

instance instModuleFinite [Finite J] [hab : Fact (a < b)] : Module.Finite k (Coord k p n a b J) :=
  moduleFinite hab.out

variable (k p n a b J)

variable {k p n a b J}


end WittKernel

end Deformation
