import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Module_Flat_of_module_fractionRing_of_isReduced_baseChange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Flat_of_module_fractionRing_of_isReduced_baseChange.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {B₁ : Type w} [CommRing B₁] [Algebra R B₁] [Module.Finite R B₁] [Module.Flat R B₁] [IsReduced (TensorProduct R K B₁)]
  {M : Type x} [AddCommGroup M] [Module R M] [Module K M] [Module B₁ M] [IsScalarTower R K M] [IsScalarTower R B₁ M] [SMulCommClass K B₁ M] :
-- imply
  Module.Flat B₁ M := by
-- proof
  let : Module (K ⊗[R] B₁) M := TensorProduct.Algebra.module
  let : Algebra B₁ (K ⊗[R] B₁) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B₁ (K ⊗[R] B₁) M :=
    IsScalarTower.of_algebraMap_smul fun b m => by
      change ((1 : K) ⊗ₜ[R] b) • m = b • m
      rw [TensorProduct.Algebra.smul_def, one_smul]
  have : IsLocalization (Algebra.algebraMapSubmonoid B₁ (nonZeroDivisors R)) (K ⊗[R] B₁) :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  have : Module.Flat B₁ (K ⊗[R] B₁) :=
    IsLocalization.flat _ (Algebra.algebraMapSubmonoid B₁ (nonZeroDivisors R))
  have : IsArtinianRing (K ⊗[R] B₁) := IsArtinianRing.of_finite K _
  have : IsSemisimpleRing (K ⊗[R] B₁) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  have : Module.Projective (K ⊗[R] B₁) M := Module.projective_of_isSemisimpleRing _ _
  exact Module.Flat.trans B₁ (K ⊗[R] B₁) M


-- created on 2026-10-05
