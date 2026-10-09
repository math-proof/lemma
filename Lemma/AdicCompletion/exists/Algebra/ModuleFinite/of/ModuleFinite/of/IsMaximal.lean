import Mathlib
import sympy.Basic

open IsLocalRing
open scoped TensorProduct Pointwise
open scoped Classical
open AdicCompletion

/--
[AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal.lean)

This file depends on FLT-specific infrastructure (semilocalComponent, tensorRingHom,
completionBaseChangeHom, tensorRingEquiv, semilocalPiEquiv, semilocalPiHom, levelMapₐ,
ext_evalₐ, etc.) that is not yet available in this codebase. The proof is stubbed with sorry.
-/

@[path]
private lemma main
  [CommRing B] [IsNoetherianRing B] [CommRing C] [Algebra B C] [Module.Finite B C]
  {𝔫 : Ideal C} [𝔫.IsMaximal] :
-- imply
  ∃ h_alg : Algebra (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B) (AdicCompletion 𝔫 C),
    ∃ h_st : IsScalarTower B (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B) (AdicCompletion 𝔫 C),
    Module.Finite (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B) (AdicCompletion 𝔫 C) ∧
      (Module.Flat B C →
        Function.Injective (algebraMap (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B) (AdicCompletion 𝔫 C))) := by
-- proof
  sorry


-- created on 2026-10-09
