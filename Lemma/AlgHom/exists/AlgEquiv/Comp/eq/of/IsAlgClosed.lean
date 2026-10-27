import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed.lean)
-/

private lemma exists_algEquiv_comp_eq
  {K : Type*}
  [Field K]
  {Ω : Type*}
  [Field Ω]
  [Algebra K Ω]
  [IsAlgClosed Ω]
  [Algebra.IsAlgebraic K Ω]
  {M : Type*} [Field M] [Algebra K M]
  (σ τ : M →ₐ[K] Ω) : ∃ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp σ = τ := by
  let : Algebra M Ω := σ.toRingHom.toAlgebra
  have : IsScalarTower K M Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (σ.commutes x).symm
  have : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) M
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := K) (L := M) (M := Ω) (E := Ω) τ
  have : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  refine ⟨AlgEquiv.ofBijective φ (AlgHom.normal_bijective K Ω Ω φ), ?_⟩
  apply AlgHom.ext
  intro m
  exact DFunLike.congr_fun hφ m


@[path]
private lemma main
  [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [Field M] [Algebra K M]
  {σ τ : M →ₐ[K] Ω} :
-- imply
  ∃ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp σ = τ :=
-- proof
  exists_algEquiv_comp_eq σ τ


-- created on 2026-10-10
