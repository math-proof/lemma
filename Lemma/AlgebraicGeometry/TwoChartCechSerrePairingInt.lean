import Mathlib
import Def.AlgebraicGeometry_TwoChartCechCupProduct
import Lemma.AlgebraicGeometry.TwoAffineOpenCoverKaehler
import Lemma.AlgebraicGeometry.TwoChartCechLaurentChart
import Def.AlgebraicGeometry_TwoChartCechSerrePairingInt

set_option autoImplicit false

noncomputable section

universe u v w

namespace TwoChartCech.Cover

variable {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R) {ι : Type w} [Fintype ι]


theorem residueSum_apply (Λ : ι → 𝒰.LaurentChart) (η : Ω[𝒰.A01⁄R]) :
    𝒰.residueSum Λ η = ∑ i, (Λ i).residue η := by
  rw [residueSum, LinearMap.sum_apply]


theorem residuesVanishOnCoboundaries_iff (Λ : ι → 𝒰.LaurentChart) :
    𝒰.ResiduesVanishOnCoboundaries Λ ↔
      (∀ ω : Ω[𝒰.A0⁄R], 𝒰.residueSum Λ (𝒰.kaehler.r0 ω) = 0) ∧
        ∀ ω : Ω[𝒰.A1⁄R], 𝒰.residueSum Λ (𝒰.kaehler.r1 ω) = 0 := by
  constructor
  · intro h
    refine ⟨fun ω => ?_, fun ω => ?_⟩
    · have hmem := h (LinearMap.mem_range_self 𝒰.kaehler.cechDiff ((ω, 0) : _ × _))
      rwa [LinearMap.mem_ker, Sections.cechDiff_apply, map_zero, zero_sub, map_neg, neg_eq_zero] at hmem
    · have hmem := h (LinearMap.mem_range_self 𝒰.kaehler.cechDiff ((0, ω) : _ × _))
      rwa [LinearMap.mem_ker, Sections.cechDiff_apply, map_zero, sub_zero] at hmem
  · rintro ⟨h0, h1⟩ _ ⟨s, rfl⟩
    rw [LinearMap.mem_ker, Sections.cechDiff_apply, map_sub, h0, h1, sub_zero]


@[simp] theorem kaehlerTrace_mk (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (η : Ω[𝒰.A01⁄R]) :
    𝒰.kaehlerTrace Λ hv (Submodule.Quotient.mk η) = ∑ i, (Λ i).residue η := by
  rw [kaehlerTrace, Sections.traceForm_mk, residueSum_apply]


theorem serrePairingInt_apply_mk (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (ω : 𝒰.kaehler.H0) (f : 𝒰.A01) :
    𝒰.serrePairingInt Λ hv ω (Submodule.Quotient.mk f) = ∑ i, (Λ i).residue (f • 𝒰.kaehler.r0 ω.val.1) := by
  rw [serrePairingInt, Sections.tracePairing_apply_mk, residueSum_apply]

theorem serrePairingInt_apply_mk' (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (ω : 𝒰.kaehler.H0) (f : 𝒰.A01) :
    𝒰.serrePairingInt Λ hv ω (Submodule.Quotient.mk f) = ∑ i, (Λ i).residue (f • 𝒰.kaehler.r1 ω.val.2) := by
  rw [serrePairingInt_apply_mk, (𝒰.kaehler.mem_H0_iff _).mp ω.2]

theorem serrePairingInt_eq_kaehlerTrace_cupProduct (Λ : ι → 𝒰.LaurentChart)
    (hv : 𝒰.ResiduesVanishOnCoboundaries Λ) (ω : 𝒰.kaehler.H0) (x : 𝒰.structureSheaf.H1) :
    𝒰.serrePairingInt Λ hv ω x = 𝒰.kaehlerTrace Λ hv (𝒰.kaehler.cupProduct ω x) := rfl

end TwoChartCech.Cover

end
