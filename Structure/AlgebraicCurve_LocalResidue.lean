import Structure.AlgebraicCurve_Place

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (v : Place K F)

/-- Uniformizer of the DVR `v.toValuationSubring` (carved host for LocalResidueData). -/
def uniformizer : F :=
  ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)

theorem ord_uniformizer : v.ord v.uniformizer = 1 := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  simpa [uniformizer] using v.ord_coe_irreducible hirr

theorem uniformizer_ne_zero : v.uniformizer ≠ 0 := by
  intro h
  simpa [h, v.ord_zero] using v.ord_uniformizer

structure LocalResidueData where

  res : F →ₗ[K] v.ResidueField

  res_of_mem : ∀ f : F, f ∈ v.toValuationSubring → res f = 0

  res_simplePole : ∀ (f : F) (hf : v.uniformizer * f ∈ v.toValuationSubring),
    res f = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩

structure CanonicalLocalResidueDataK extends v.LocalResidueData where

  res_higherPoleMonomial : ∀ (n : ℕ), 1 ≤ n → res (v.uniformizer ^ (n + 1))⁻¹ = 0

end Place

end AlgebraicCurve
