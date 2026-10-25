import Mathlib
import Instance.GaloisRep_ComplexConjugation

set_option autoImplicit false

noncomputable def complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift

noncomputable def complexConjAlgEquiv : ℂ ≃ₐ[ℚ] ℂ :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun x => map_ratCast (starRingEnd ℂ) x


noncomputable def complexConjugation : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ :=
  AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℂ) (AlgebraicClosure ℚ) complexConjAlgEquiv


namespace ExtCitation

noncomputable def archimedeanDecomposition :
    Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  Subgroup.zpowers complexConjugation

noncomputable def archimedeanGen : archimedeanDecomposition :=
  ⟨complexConjugation, Subgroup.mem_zpowers complexConjugation⟩

noncomputable def archimedeanLoc :
    archimedeanDecomposition →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  archimedeanDecomposition.subtype

end ExtCitation
