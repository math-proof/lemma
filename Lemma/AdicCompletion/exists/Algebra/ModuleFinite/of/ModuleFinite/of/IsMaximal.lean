import sympy.Basic
import Mathlib
import Lemma.AdicCompletion.Support.Exists

open IsLocalRing AdicCompletion

/--
[AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal.lean)
-/
@[path]
private lemma main
-- given
  [CommRing B] [IsNoetherianRing B] [CommRing C] [Algebra B C] [Module.Finite B C]
  {𝔫 : Ideal C} [𝔫.IsMaximal] :
-- imply
  Nonempty (Σ'
      (_ : Algebra (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B) (AdicCompletion 𝔫 C))
      (_ : IsScalarTower B (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B) (AdicCompletion 𝔫 C)),
      Module.Finite (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B) (AdicCompletion 𝔫 C) ∧
        (Module.Flat B C →
          Function.Injective
            (algebraMap (AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B)
              (AdicCompletion 𝔫 C)))) :=
-- proof
  exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal B C 𝔫


-- created on 2026-10-09
