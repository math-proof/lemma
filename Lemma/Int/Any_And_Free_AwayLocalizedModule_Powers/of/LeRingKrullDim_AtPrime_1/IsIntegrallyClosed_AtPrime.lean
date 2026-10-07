import Mathlib
import sympy.Basic


/--
[Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one.lean)
-/
@[main]
private lemma main
  {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
  {𝔭 : Ideal A} [𝔭.IsPrime]
  {B : Type u} [AddCommGroup B] [Module A B] [Module.Finite A B] [NoZeroSMulDivisors A B]
-- given
  (h𝔭ic : IsIntegrallyClosed (Localization.AtPrime 𝔭))
  (h𝔭dim : ringKrullDim (Localization.AtPrime 𝔭) ≤ 1) :
-- imply
  ∃ f : A, f ∉ 𝔭 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) B) := by
-- proof
  classical
  set Aₚ := Localization.AtPrime 𝔭 with hAₚ
  have : IsNoetherianRing Aₚ := IsLocalization.isNoetherianRing 𝔭.primeCompl Aₚ inferInstance
  have : IsDomain Aₚ := IsLocalization.isDomain_localization 𝔭.primeCompl_le_nonZeroDivisors
  have : Ring.KrullDimLE 1 Aₚ := Ring.krullDimLE_iff.mpr h𝔭dim
  have : Ring.DimensionLEOne Aₚ := ⟨fun hne hp => Ideal.IsPrime.isMaximal_of_ne_bot hp hne⟩
  have : IsDedekindRing Aₚ := { (inferInstance : IsNoetherian Aₚ Aₚ), (inferInstance : Ring.DimensionLEOne Aₚ), h𝔭ic with }
  have : IsDedekindDomain Aₚ := {}
  have : IsPrincipalIdealRing Aₚ := inferInstance
  have : Module.IsTorsionFree A B := inferInstance
  have : Module.Finite Aₚ (LocalizedModule 𝔭.primeCompl B) := inferInstance
  have : Module.IsTorsionFree Aₚ (LocalizedModule 𝔭.primeCompl B) := inferInstance
  have : Module.Free Aₚ (LocalizedModule 𝔭.primeCompl B) := Module.free_of_finite_type_torsion_free'
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers 𝔭.primeCompl
    (LocalizedModule.mkLinearMap 𝔭.primeCompl B) (Localization.AtPrime 𝔭)
  exact ⟨r, hr, hfree⟩


-- created on 2026-10-05
