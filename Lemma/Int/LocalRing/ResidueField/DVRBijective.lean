import Mathlib
import Initialize.Tactic.Attr.Basic


namespace DVRResidue

/--
[residueFieldMapAlgHom_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVRBijective.lean)
-/
@[path]
lemma residueFieldMapAlgHom_bijective
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [Algebra.Etale A B] [HenselianLocalRing C] :
-- imply
  Function.Bijective
    (residueFieldMapAlgHom (A :=
-- proof
  ⟨residueFieldMapAlgHom_injective, residueFieldMapAlgHom_surjective⟩

end DVRResidue

namespace DVRResidue

/--
[exists_algEquiv_lift_residueField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVRBijective.lean)
-/
@[path]
lemma exists_algEquiv_lift_residueField
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [Algebra.Etale A B] [Algebra.Etale A C] [HenselianLocalRing B] [HenselianLocalRing C]
-- given
  (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField C) :
-- imply
  ∃ e' : B ≃ₐ[A] C,
    residueFieldMapAlgHom e'.toAlgHom = e.toAlgHom ∧
    residueFieldMapAlgHom e'.symm.toAlgHom = e.symm.toAlgHom := by
-- proof
  obtain ⟨f, hf⟩ :=
    residueFieldMapAlgHom_surjective (A := A) (B := B) (C := C) e.toAlgHom
  obtain ⟨g, hg⟩ :=
    residueFieldMapAlgHom_surjective (A := A) (B := C) (C := B) e.symm.toAlgHom
  have hfg : f.comp g = AlgHom.id A C := by
    apply residueFieldMapAlgHom_injective (A := A) (B := C) (C := C)
    rw [residueFieldMapAlgHom_comp, hf, hg, residueFieldMapAlgHom_id]
    ext x
    simp
  have hgf : g.comp f = AlgHom.id A B := by
    apply residueFieldMapAlgHom_injective (A := A) (B := B) (C := B)
    rw [residueFieldMapAlgHom_comp, hf, hg, residueFieldMapAlgHom_id]
    ext x
    simp
  refine ⟨AlgEquiv.ofAlgHom f g hfg hgf, ?_, ?_⟩
  · exact hf
  · change residueFieldMapAlgHom g = e.symm.toAlgHom
    exact hg

end DVRResidue


-- created on 2026-10-20
-- updated on 2026-10-26
