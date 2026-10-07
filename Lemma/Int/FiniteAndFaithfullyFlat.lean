import Mathlib
import sympy.Basic

open TensorProduct

/--
[Module_finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct.lean)
-/
@[main]
private lemma main
  {R : Type u} [CommRing R]
  {W : Type v} [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W]
  {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite W (W ⊗[R] M)] [Module.FaithfullyFlat W (W ⊗[R] M)] :
-- imply
  Module.Finite R M ∧ Module.FaithfullyFlat R M := by
-- proof
  have hfin : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat W
  have hflat : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M W
  refine ⟨hfin, (Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality R M).mpr ⟨hflat, ?_⟩⟩
  intro N _ _ hN

  have e₁ : (W ⊗[R] M) ⊗[W] (W ⊗[R] N) ≃ₗ[W] (W ⊗[R] M) ⊗[R] N :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R W W (W ⊗[R] M) N
  have e₂ : (W ⊗[R] M) ⊗[R] N ≃ₗ[R] W ⊗[R] (M ⊗[R] N) := TensorProduct.assoc R W M N
  have : Subsingleton (W ⊗[R] (M ⊗[R] N)) := inferInstance
  have h1 : Subsingleton ((W ⊗[R] M) ⊗[W] (W ⊗[R] N)) :=
    (e₁.toEquiv.trans e₂.toEquiv).subsingleton
  have h2 : Subsingleton (W ⊗[R] N) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right W (W ⊗[R] M)).mp h1
  exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R W).mp h2


-- created on 2026-10-05
