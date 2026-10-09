import Mathlib
import sympy.Basic

open Algebra

/--
[Algebra_IsSmoothAt_flat_localization_atPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsSmoothAt_flat_localization_atPrime.lean)
-/
@[path]
private lemma main
  {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
  {p : Ideal A} [p.IsPrime] [Algebra.IsSmoothAt R p] :
-- imply
  Module.Flat R (Localization.AtPrime p) := by
-- proof
  obtain ⟨f, hf, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R p
  have := hsm
  have : Module.Flat R (Localization.Away f) := Algebra.Smooth.flat R _
  have hle : Submonoid.powers f ≤ p.primeCompl := by
    rintro x ⟨n, rfl⟩
    exact fun h => hf (‹p.IsPrime›.mem_of_pow_mem n h)
  let : Algebra (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f) p.primeCompl hle
  have : IsScalarTower A (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers f) p.primeCompl hle
  have : IsLocalization ((p.primeCompl).map (algebraMap A (Localization.Away f))) (Localization.AtPrime p) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers f) p.primeCompl hle
  have : Module.Flat (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p) ((p.primeCompl).map (algebraMap A (Localization.Away f)))
  have : IsScalarTower R (Localization.Away f) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime p) r,
        IsScalarTower.algebraMap_apply R A (Localization.Away f) r,
        ← IsScalarTower.algebraMap_apply A (Localization.Away f) (Localization.AtPrime p)])
  exact Module.Flat.trans R (Localization.Away f) (Localization.AtPrime p)


-- created on 2026-10-05
