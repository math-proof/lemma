module

public import Mathlib

@[expose] public section

set_option autoImplicit false

noncomputable def complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift

noncomputable def complexConjAlgEquiv : ℂ ≃ₐ[ℚ] ℂ :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun x => map_ratCast (starRingEnd ℂ) x

local instance isAlgebraicQbar_cc : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_cc : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance normalQbar_cc : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
noncomputable local instance instDecEqQbar_cc : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

noncomputable local instance instAlgebraQbarComplex : Algebra (AlgebraicClosure ℚ) ℂ :=
  complexEmbedding.toRingHom.toAlgebra
local instance instTowerQbarComplex : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

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
