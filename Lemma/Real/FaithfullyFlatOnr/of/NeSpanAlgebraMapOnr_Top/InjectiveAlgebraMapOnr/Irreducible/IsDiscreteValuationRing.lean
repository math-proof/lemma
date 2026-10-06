import Mathlib
import sympy.Basic


/--
[CerednikDrinfeld_Onr_faithfullyFlat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Onr_faithfullyFlat.lean)
-/
@[main]
private lemma main
  [CommRing 𝒪] [IsDomain 𝒪] [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr]
  {π : 𝒪}
-- given
  (hdvr : IsDiscreteValuationRing 𝒪)
  (hπ : Irreducible π)
  (hinj : Function.Injective (algebraMap 𝒪 Onr))
  (hproper : Ideal.span {algebraMap 𝒪 Onr π} ≠ ⊤) :
-- imply
  Module.FaithfullyFlat 𝒪 Onr := by
-- proof
  classical
  haveI := hdvr

  haveI : Module.IsTorsionFree 𝒪 Onr :=
    Module.IsTorsionFree.comap (algebraMap 𝒪 Onr)
      (fun r hr => by
        have hr0 : r ≠ 0 := by
          rintro rfl
          exact not_isRegular_zero hr
        exact IsRegular.of_ne_zero ((map_ne_zero_iff _ hinj).mpr hr0))
      (fun r m => (Algebra.smul_def r m).symm)
  haveI : Module.Flat 𝒪 Onr := inferInstance

  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal 𝒪 Onr).mpr ⟨inferInstance, ?_⟩
  intro I hI htop
  have hmax : IsLocalRing.maximalIdeal 𝒪 = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hle : I ≤ Ideal.span {π} := hmax ▸ IsLocalRing.le_maximalIdeal hI

  have hsub : (I • (⊤ : Submodule 𝒪 Onr) : Submodule 𝒪 Onr) ≤
      (Ideal.span {algebraMap 𝒪 Onr π}).restrictScalars 𝒪 := by
    refine Submodule.smul_le.mpr ?_
    intro r hr x _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (hle hr)
    change (c * π) • x ∈ Ideal.span {algebraMap 𝒪 Onr π}
    rw [Algebra.smul_def, map_mul, mul_assoc, mul_comm (algebraMap 𝒪 Onr π), ← mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  apply hproper
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (I • (⊤ : Submodule 𝒪 Onr) : Submodule 𝒪 Onr) := by rw [htop]; trivial
  exact hsub hx


-- created on 2026-10-05
