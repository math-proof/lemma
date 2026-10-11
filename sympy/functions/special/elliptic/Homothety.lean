import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Homothetic complex period lattices

Two period lattices are homothetic when one is a nonzero complex scaling of the other.
-/

open scoped Pointwise

namespace PeriodPair

/-- Two period pairs are homothetic when their lattices differ by a nonzero scaling. -/
def IsHomothetic (L L' : PeriodPair) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)

/-- Homothety of period pairs is reflexive. -/
theorem IsHomothetic.refl (L : PeriodPair) : IsHomothetic L L :=
  ⟨1, one_ne_zero, (one_smul ℂ (L.lattice : Set ℂ)).symm⟩

/-- Homothety of period pairs is symmetric. -/
theorem IsHomothetic.symm {L L' : PeriodPair} (h : IsHomothetic L L') :
    IsHomothetic L' L := by
  obtain ⟨c, hc, hLat⟩ := h
  exact ⟨c⁻¹, inv_ne_zero hc, by rw [hLat, inv_smul_smul₀ hc]⟩

/-- Homothety of period pairs is transitive. -/
theorem IsHomothetic.trans {L₁ L₂ L₃ : PeriodPair}
    (h₁₂ : IsHomothetic L₁ L₂) (h₂₃ : IsHomothetic L₂ L₃) :
    IsHomothetic L₁ L₃ := by
  obtain ⟨c₁, hc₁, h₁₂⟩ := h₁₂
  obtain ⟨c₂, hc₂, h₂₃⟩ := h₂₃
  exact ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, by rw [h₂₃, h₁₂, smul_smul]⟩

/-- Homothety of period pairs is an equivalence relation. -/
theorem isHomothetic_equivalence : Equivalence IsHomothetic :=
  ⟨IsHomothetic.refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

end PeriodPair
