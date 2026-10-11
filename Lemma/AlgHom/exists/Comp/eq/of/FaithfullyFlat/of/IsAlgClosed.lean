import Mathlib
import sympy.Basic


/--
[AlgHom_exists_comp_eq_of_faithfullyFlat_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_exists_comp_eq_of_faithfullyFlat_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K] [IsAlgClosed K]
  {R : Type v} [CommRing R] [Algebra K R]
  {S : Type w} [CommRing S] [Algebra K S] [Module.Finite K S] [Algebra R S] [IsScalarTower K R S] [Module.FaithfullyFlat R S]
  {x : R →ₐ[K] K} :
-- imply
  ∃ y : S →ₐ[K] K, y.comp (IsScalarTower.toAlgHom K R S) = x := by
-- proof
  classical

    have hxs : Function.Surjective x := fun c => ⟨algebraMap K R c, x.commutes c⟩
    have hmax : (RingHom.ker x).IsMaximal := RingHom.ker_isMaximal_of_surjective x hxs

    set I : Ideal S := Ideal.map (algebraMap R S) (RingHom.ker x) with hI
    have hI_ne : I ≠ ⊤ := by
      have h := Module.FaithfullyFlat.submodule_ne_top (R := R) (M := S) hmax
      rw [Ideal.smul_top_eq_map] at h
      intro htop
      apply h
      rw [hI] at htop
      rw [htop]
      rfl
    obtain ⟨𝔫, h𝔫max, hI𝔫⟩ := Ideal.exists_le_maximal I hI_ne

    have : 𝔫.IsMaximal := h𝔫max
    have : Module.Finite K (S ⧸ 𝔫) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K 𝔫).toLinearMap (Ideal.Quotient.mkₐ_surjective K 𝔫)
    have : Algebra.IsIntegral K (S ⧸ 𝔫) := Algebra.IsIntegral.of_finite K (S ⧸ 𝔫)
    have hbij : Function.Bijective (algebraMap K (S ⧸ 𝔫)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : K ≃ₐ[K] S ⧸ 𝔫 := AlgEquiv.ofBijective (Algebra.ofId K (S ⧸ 𝔫)) hbij
    refine ⟨(e.symm : S ⧸ 𝔫 →ₐ[K] K).comp (Ideal.Quotient.mkₐ K 𝔫), ?_⟩
    ext r

    have hr : algebraMap R S r - algebraMap K S (x r) ∈ 𝔫 := by
      apply hI𝔫
      have hmem : r - algebraMap K R (x r) ∈ RingHom.ker x := by
        rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
      have := Ideal.mem_map_of_mem (algebraMap R S) hmem
      rwa [map_sub, ← IsScalarTower.algebraMap_apply] at this
    have hq : Ideal.Quotient.mkₐ K 𝔫 (algebraMap R S r) = algebraMap K (S ⧸ 𝔫) (x r) := by
      rwa [← sub_eq_zero, IsScalarTower.algebraMap_apply K S (S ⧸ 𝔫), Ideal.Quotient.mkₐ_eq_mk,
        ← Ideal.Quotient.algebraMap_eq, ← map_sub, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

    rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hq]
    show e.symm (algebraMap K (S ⧸ 𝔫) (x r)) = x r
    have : algebraMap K (S ⧸ 𝔫) (x r) = e (x r) := rfl
    rw [this, AlgEquiv.symm_apply_apply]


-- created on 2026-10-10
