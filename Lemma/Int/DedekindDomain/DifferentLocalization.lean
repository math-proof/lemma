import Mathlib
import sympy.Basic
import Instance.RingTheory.DedekindDomain.DifferentLocalization
open FractionalIdeal


variable (A K : Type*) (L : Type u) (B : Type*) [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L] [IsFractionRing B L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)
variable (SB : Type*) [CommRing SB] [Algebra B SB] [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] [Algebra (Localization.subalgebra.ofField K S hS) SB] [Algebra SB L] [Algebra A SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A B SB] [IsScalarTower B SB L] [IsScalarTower A (Localization.subalgebra.ofField K S hS) L] [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L] [IsScalarTower (Localization.subalgebra.ofField K S hS) K L] [IsFractionRing SB L] [IsDedekindDomain SB] [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB] [Module.IsTorsionFree B SB] [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]
/--
[span_coe_restrictScalars_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentLocalization.lean)
-/
@[path]
private lemma span_coe_restrictScalars_eq (N : Submodule B L) :
  Submodule.span Aₛ (N : Set L) = (Submodule.span SB (N : Set L)).restrictScalars Aₛ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact Submodule.subset_span hx
  · intro y hy
    rw [Submodule.restrictScalars_mem] at hy
    have key : ∀ z ∈ Submodule.span SB (N : Set L), ∃ w ∈ N, ∃ a ∈ S,
      (algebraMap A B a) • z = w := by
      intro z hz
      refine Submodule.span_induction
        (p := fun z _ => ∃ w ∈ N, ∃ a ∈ S, (algebraMap A B a) • z = w) ?_ ?_ ?_ ?_ hz
      · intro z hz
        exact ⟨z, SetLike.mem_coe.mp hz, 1, S.one_mem, by simp⟩
      · exact ⟨0, N.zero_mem, 1, S.one_mem, by simp⟩
      · intro x₁ x₂ _ _ ih₁ ih₂
        obtain ⟨w₁, hw₁, a₁, ha₁, h₁⟩ := ih₁
        obtain ⟨w₂, hw₂, a₂, ha₂, h₂⟩ := ih₂
        refine ⟨(algebraMap A B a₂) • w₁ + (algebraMap A B a₁) • w₂,
          N.add_mem (N.smul_mem _ hw₁) (N.smul_mem _ hw₂),
          a₁ * a₂, S.mul_mem ha₁ ha₂, ?_⟩
        have h₁' : algebraMap B L (algebraMap A B a₁) * x₁ = w₁ := by
          rw [← Algebra.smul_def]; exact h₁
        have h₂' : algebraMap B L (algebraMap A B a₂) * x₂ = w₂ := by
          rw [← Algebra.smul_def]; exact h₂
        simp only [map_mul, Algebra.smul_def, map_mul]
        linear_combination (algebraMap B L (algebraMap A B a₂)) * h₁' +
          (algebraMap B L (algebraMap A B a₁)) * h₂'
      · intro r z _ ih
        obtain ⟨w, hw, a, ha, hden⟩ := ih
        obtain ⟨⟨b, sm⟩, hr⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B S) r
        obtain ⟨s₁, hs₁, heq⟩ :=
          Submonoid.mem_map.mp (show (sm : B) ∈ S.map (algebraMap A B) from sm.2)
        refine ⟨b • w, N.smul_mem b hw, s₁ * a, S.mul_mem hs₁ ha, ?_⟩
        have hden' : algebraMap B L (algebraMap A B a) * z = w := by
          rw [← Algebra.smul_def]; exact hden
        have hrL : algebraMap SB L r * algebraMap B L (algebraMap A B s₁) =
          algebraMap B L b := by
          have h := congrArg (algebraMap SB L) hr
          simp only [map_mul] at h
          rwa [← IsScalarTower.algebraMap_apply B SB L,
            ← IsScalarTower.algebraMap_apply B SB L, ← heq] at h
        simp only [map_mul, Algebra.smul_def]
        linear_combination (algebraMap B L (algebraMap A B a) * z) * hrL +
          (algebraMap B L b) * hden'
    obtain ⟨w, hw, a, ha, hden⟩ := key y hy
    have hunit : IsUnit (algebraMap A Aₛ a) := IsLocalization.map_units Aₛ ⟨a, ha⟩
    obtain ⟨u, hu⟩ := hunit
    have htw : (algebraMap A Aₛ a) • y = w := by
      rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply A Aₛ L,
        IsScalarTower.algebraMap_apply A B L, ← Algebra.smul_def]
      exact hden
    have hy_eq : y = ((u⁻¹ : Units Aₛ) : Aₛ) • w := by
      change y = (u⁻¹ : Units Aₛ) • w
      rw [eq_inv_smul_iff]
      change (u : Aₛ) • y = w
      rwa [hu]
    rw [hy_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (SetLike.mem_coe.mpr hw))
omit K S hS SB [Algebra A K] [Algebra K L] [IsScalarTower A K L]
  [IsFractionRing A K] [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L] [IsFractionRing B L] [IsDedekindDomain A]
  [IsDedekindDomain B] [Module.IsTorsionFree A B] [CommRing SB] [Algebra B SB]
  [IsLocalization (Algebra.algebraMapSubmonoid B S) SB]
  [Algebra (Localization.subalgebra.ofField K S hS) SB] [Algebra SB L]
  [Algebra A SB]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB]
  [IsScalarTower A B SB] [IsScalarTower B SB L]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) L]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) K L]
  [IsFractionRing SB L] [IsDedekindDomain SB]
  [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB]
  [Module.IsTorsionFree B SB]
  [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L] in

variable (A K : Type*) (L : Type u) (B : Type*) [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L] [IsFractionRing B L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)
variable (SB : Type*) [CommRing SB] [Algebra B SB] [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] [Algebra (Localization.subalgebra.ofField K S hS) SB] [Algebra SB L] [Algebra A SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A B SB] [IsScalarTower B SB L] [IsScalarTower A (Localization.subalgebra.ofField K S hS) L] [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L] [IsScalarTower (Localization.subalgebra.ofField K S hS) K L] [IsFractionRing SB L] [IsDedekindDomain SB] [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB] [Module.IsTorsionFree B SB] [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]
/--
[fg_restrictScalars_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentLocalization.lean)
-/
@[path]
finite over `A`. The finiteness hypothesis is taken explicitly so that the fraction
field `K` does not need to be named in this lemma's own signature
(universe-level capture). -/
private lemma fg_restrictScalars_one (hfin : Module.Finite A B) :
  ((1 : Submodule B L).restrictScalars A).FG := by
  have := hfin
  have hM : (1 : Submodule B L).restrictScalars A =
    ((Algebra.linearMap B L).restrictScalars A).range := by
    ext x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_range]
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := Submodule.mem_one.mp hx
      exact ⟨b, hb⟩
    · rintro ⟨b, rfl⟩
      exact Submodule.mem_one.mpr ⟨b, rfl⟩
  rw [hM]
  exact Submodule.fg_range _
omit A K S hS [CommRing A] [Field K] [Algebra A K] [Algebra A B] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K]
  [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L]
  [IsFractionRing B L] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]
  [IsLocalization (Algebra.algebraMapSubmonoid B S) SB]
  [Algebra (Localization.subalgebra.ofField K S hS) SB] [Algebra A SB]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB]
  [IsScalarTower A B SB]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) L]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) K L]
  [IsFractionRing SB L] [IsDedekindDomain SB]
  [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB]
  [Module.IsTorsionFree B SB]
  [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L] in

variable (A K : Type*) (L : Type u) (B : Type*) [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L] [IsFractionRing B L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)
variable (SB : Type*) [CommRing SB] [Algebra B SB] [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] [Algebra (Localization.subalgebra.ofField K S hS) SB] [Algebra SB L] [Algebra A SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A B SB] [IsScalarTower B SB L] [IsScalarTower A (Localization.subalgebra.ofField K S hS) L] [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L] [IsScalarTower (Localization.subalgebra.ofField K S hS) K L] [IsFractionRing SB L] [IsDedekindDomain SB] [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB] [Module.IsTorsionFree B SB] [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]
/--
[span_coe_one_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentLocalization.lean)
-/
@[path]
private lemma span_coe_one_eq_one :
  Submodule.span SB ((1 : Submodule B L) : Set L) = 1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp (SetLike.mem_coe.mp hx)
    exact Submodule.mem_one.mpr ⟨algebraMap B SB b, by
      rw [← IsScalarTower.algebraMap_apply B SB L]
      exact hb⟩
  · rw [Submodule.one_le]
    exact Submodule.subset_span
      (SetLike.mem_coe.mpr (Submodule.mem_one.mpr ⟨1, map_one _⟩))
omit [IsFractionRing B L] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Algebra A SB]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB]
  [IsScalarTower A B SB] [IsFractionRing SB L] [IsDedekindDomain SB]
  [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB]
  [Module.IsTorsionFree B SB]
  [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L] in

variable (A K : Type*) (L : Type u) (B : Type*) [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L] [IsFractionRing B L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)
variable (SB : Type*) [CommRing SB] [Algebra B SB] [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] [Algebra (Localization.subalgebra.ofField K S hS) SB] [Algebra SB L] [Algebra A SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A B SB] [IsScalarTower B SB L] [IsScalarTower A (Localization.subalgebra.ofField K S hS) L] [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L] [IsScalarTower (Localization.subalgebra.ofField K S hS) K L] [IsFractionRing SB L] [IsDedekindDomain SB] [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB] [Module.IsTorsionFree B SB] [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]
/--
[traceDual_span_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentLocalization.lean)
-/
@[path]
over `Aₛ`. -/
private lemma traceDual_span_eq :
  Submodule.traceDual Aₛ K (1 : Submodule SB L) =
    Submodule.span SB ((Submodule.traceDual A K (1 : Submodule B L)) : Set L) := by
  have hFG := fg_restrictScalars_one A L B (IsIntegralClosure.finite A K L B)
  have h888 := LinearMap.BilinForm.dualSubmodule_span_localization
    (Algebra.traceForm K L) S hS ((1 : Submodule B L).restrictScalars A) hFG
  -- Unfold the `let Aₛ` in #888 so that rewrite rules stated with `Aₛ` match.
  have h888u : (Algebra.traceForm K L).dualSubmodule
    (Submodule.span Aₛ ((((1 : Submodule B L).restrictScalars A)) : Set L)) =
    Submodule.span Aₛ ((((Algebra.traceForm K L).dualSubmodule
      ((1 : Submodule B L).restrictScalars A))) : Set L) := h888
  have hset1 : ((((1 : Submodule B L).restrictScalars A : Submodule A L)) : Set L) =
    ((1 : Submodule B L) : Set L) :=
    Submodule.coe_restrictScalars A _
  have hdual : (Algebra.traceForm K L).dualSubmodule
    ((1 : Submodule B L).restrictScalars A) =
    ((Submodule.traceDual A K (1 : Submodule B L)).restrictScalars A) :=
    (Submodule.restrictScalars_traceDual).symm
  rw [hset1, hdual, Submodule.coe_restrictScalars A _] at h888u
  rw [span_coe_restrictScalars_eq A K L B S hS SB _,
    span_coe_restrictScalars_eq A K L B S hS SB _,
    span_coe_one_eq_one L B SB] at h888u
  rw [← Submodule.restrictScalars_traceDual] at h888u
  exact (Submodule.restrictScalars_inj Aₛ SB L).mp h888u
namespace FractionalIdeal
omit [Module.IsTorsionFree A B] [Algebra A SB]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB]
  [IsScalarTower A B SB]
  [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB] in

namespace FractionalIdeal

/--
[extendedHom_dual_one_eq_dual_one_ofField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentLocalization.lean)
-/
@[path]
lemma extendedHom_dual_one_eq_dual_one_ofField
  [CommRing A] [Field K] [CommRing B] [Algebra A K] [Algebra A B] [IsFractionRing A K] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [CommRing SB] [Algebra B SB] [Algebra A SB] [IsScalarTower A B SB] [IsDedekindDomain SB] [Module.IsTorsionFree B SB]
  {L : Type u} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L] [IsFractionRing B L] [Algebra SB L] [IsScalarTower B SB L] [IsFractionRing SB L]
  {S : Submonoid A} [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] [Algebra (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) L] [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L] [IsScalarTower (Localization.subalgebra.ofField K S hS) K L] [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB] [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]
-- given
  (hS : S ≤ nonZeroDivisors A) :
-- imply
  extendedHom L SB (dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) =
    dual Aₛ K (1 : FractionalIdeal (nonZeroDivisors SB) L) := by
-- proof
  have hinjB : Function.Injective (algebraMap B SB) := by
    apply Function.Injective.of_comp (f := (algebraMap SB L))
    change Function.Injective (((algebraMap SB L).comp (algebraMap B SB) : B →+* L))
    rw [← IsScalarTower.algebraMap_eq B SB L]
    exact IsFractionRing.injective B L
  have hf : (nonZeroDivisors B) ≤ Submonoid.comap (algebraMap B SB) (nonZeroDivisors SB) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap B SB) hinjB
  have hmap : IsLocalization.map (R := B) (M := nonZeroDivisors B) (S := L)
    (P := SB) (T := nonZeroDivisors SB) L (algebraMap B SB) hf = RingHom.id L := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors B)
    ext b
    simp only [RingHom.comp_apply, IsLocalization.map_eq, RingHom.id_apply]
    rw [IsScalarTower.algebraMap_apply B SB L]
  have eimg : (⇑(RingHom.id L) '' ((dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) :
    Set L)) = ((Submodule.traceDual A K (1 : Submodule B L)) : Set L) := by
    have hsub : ((dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) : Submodule B L) =
      Submodule.traceDual A K (1 : Submodule B L) :=
      FractionalIdeal.coe_dual_one A K L B
    have s1 : ((dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) : Set L) =
      ((Submodule.traceDual A K (1 : Submodule B L)) : Set L) :=
      congrArg (fun s : Submodule B L => (s : Set L)) hsub
    rw [s1]
    exact Set.image_id _
  rw [← coeToSubmodule_inj, extendedHom'_apply, coe_extended_eq_span, hmap]
  have hR : ((dual Aₛ K (1 : FractionalIdeal (nonZeroDivisors SB) L)) : Submodule SB L) =
    Submodule.traceDual Aₛ K (1 : Submodule SB L) :=
    FractionalIdeal.coe_dual_one Aₛ K L SB
  rw [eimg, hR]
  exact (traceDual_span_eq A K L B S hS SB).symm
end FractionalIdeal
omit [IsFractionRing B L] [Algebra A SB]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB]
  [IsScalarTower A B SB] in

end FractionalIdeal

/--
[Ideal.map_differentIdeal_eq_localization_ofField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentLocalization.lean)
-/
@[path]
lemma Ideal.map_differentIdeal_eq_localization_ofField
  [CommRing A] [Field K] [CommRing B] [Algebra A K] [Algebra A B] [IsFractionRing A K] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [CommRing SB] [Algebra B SB] [Algebra A SB] [IsScalarTower A B SB] [IsDedekindDomain SB] [Module.IsTorsionFree B SB]
  {L : Type u} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L] [Algebra SB L] [IsScalarTower B SB L] [IsFractionRing SB L] [IsFractionRing B L]
  {S : Submonoid A} [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] [Algebra (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) L] [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L] [IsScalarTower (Localization.subalgebra.ofField K S hS) K L] [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB] [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]
-- given
  (hS : S ≤ nonZeroDivisors A) :
-- imply
  Ideal.map (algebraMap B SB) (differentIdeal A B) = differentIdeal Aₛ SB := by
-- proof
  have hfinB : Module.Finite A B := IsIntegralClosure.finite A K L B
  have hfinSB : Module.Finite Aₛ SB := IsIntegralClosure.finite Aₛ K L SB
  rw [← FractionalIdeal.coeIdeal_inj (R := SB) (K := L),
    ← FractionalIdeal.extendedHom_coeIdeal_eq_map (A := B) (K := L) L SB,
    coeIdeal_differentIdeal A K L B,
    map_inv₀, FractionalIdeal.extendedHom_dual_one_eq_dual_one_ofField A K L B S hS SB,
    ← coeIdeal_differentIdeal Aₛ K L SB]


-- created on 2026-10-20
-- updated on 2026-10-23
