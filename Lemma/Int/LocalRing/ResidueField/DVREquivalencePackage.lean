import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.DiscreteValuationRing.Monogenic
import Lemma.Int.DiscreteValuationRing.Monogenic
import Lemma.Int.LocalRing.ResidueField.AdjoinRootLift
import Def.RingTheory.LocalRing.ResidueField.AdjoinRootLift.Part3


namespace DVRResidue

/--
[residueField_partial_equivalence_package_of_isAdicComplete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVREquivalencePackage.lean)
-/
@[path]
lemma residueField_partial_equivalence_package_of_isAdicComplete
  {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {B₁ B₂ : Type u} [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁] [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂] [Algebra A B₁] [Algebra A B₂] [Module.Finite A B₁] [Module.Finite A B₂] [IsLocalHom (algebraMap A B₁)] [IsLocalHom (algebraMap A B₂)] [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁] [IsAdicComplete (IsLocalRing.maximalIdeal B₂) B₂] [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₁)] [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₂)]
-- given
  (hfin₁ : Module.finrank A B₁ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₁))
  (hfin₂ : Module.finrank A B₂ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B₂)) :
-- imply
  Function.Bijective (residueFieldMapAlgHom (A := by
-- proof
  let _ : Algebra.Etale A B₁ :=
    IsDiscreteValuationRing.etale_of_isSeparable_residueField_of_finrank_eq hfin₁
  let _ : Algebra.Etale A B₂ :=
    IsDiscreteValuationRing.etale_of_isSeparable_residueField_of_finrank_eq hfin₂
  refine ⟨residueFieldMapAlgHom_bijective_of_isAdicComplete, ?_, ?_⟩
  · intro L _ _ _ _
    exact exists_finite_dvr_extension_residueField_algEquiv L
  · intro e
    exact exists_algEquiv_lift_residueField_of_isAdicComplete e

end DVRResidue


-- created on 2026-10-20
-- updated on 2026-10-26
