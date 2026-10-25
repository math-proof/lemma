import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Prop34BlowupProperties.Part4
open Polynomial AlgebraicGeometry Prop34Blowup


namespace Prop34Blowup

/--
[scaleAlgHom_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean)
-/
@[path]
lemma scaleAlgHom_one
  [CommRing R] :
-- imply
  scaleAlgHom (1 : R) = AlgHom.id R R[X] := by
-- proof
  ext; unfold scaleAlgHom; simp [map_one, one_mul]

end Prop34Blowup

namespace Prop34Blowup

/--
[scaleAlgHom_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean)
-/
@[path]
lemma scaleAlgHom_comp
  [CommRing R]
  {c₁ c₂ : R} :
-- imply
  (scaleAlgHom c₁).comp (scaleAlgHom c₂) = scaleAlgHom (c₁ * c₂) := by
-- proof
  ext
  unfold scaleAlgHom
  simp only [AlgHom.comp_apply, aeval_X]
  simp only [aeval_def, eval₂_mul, eval₂_C, eval₂_X, Polynomial.algebraMap_eq]
  rw [← mul_assoc, ← C_mul, mul_comm c₂ c₁]

end Prop34Blowup

namespace Prop34Blowup

/--
[scaleOnGraded_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean)
-/
@[path]
lemma scaleOnGraded_one
  [CommRing R]
  {I : Ideal R} :
-- imply
  scaleOnGraded I (1 : R) = RingHom.id (assocGradedRing I) := by
-- proof
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [scaleOnGraded, RingHom.comp_apply, Ideal.Quotient.lift_mk]
  show Ideal.Quotient.mk _ (scaleOnRees I 1 x) = Ideal.Quotient.mk _ x
  congr 1
  apply Subtype.ext
  show scaleAlgHom 1 x.val = x.val
  rw [show scaleAlgHom (1 : R) = AlgHom.id R R[X] from scaleAlgHom_one]
  simp

end Prop34Blowup

namespace Prop34Blowup

/--
[scaleOnGraded_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean)
-/
@[path]
lemma scaleOnGraded_comp
  [CommRing R]
  {I : Ideal R}
  {c₁ c₂ : R} :
-- imply
  scaleOnGraded I (c₁ * c₂) = (scaleOnGraded I c₁).comp (scaleOnGraded I c₂) := by
-- proof
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [scaleOnGraded, RingHom.comp_apply, Ideal.Quotient.lift_mk]
  show Ideal.Quotient.mk _ (scaleOnRees I (c₁ * c₂) x) =
    Ideal.Quotient.mk _ (scaleOnRees I c₁ (scaleOnRees I c₂ x))
  congr 1
  apply Subtype.ext
  show scaleAlgHom (c₁ * c₂) x.val = scaleAlgHom c₁ (scaleAlgHom c₂ x.val)
  rw [← AlgHom.comp_apply, ← scaleAlgHom_comp]

end Prop34Blowup

namespace Prop34Blowup

/--
[proposition_34_blowup_properties](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean)
-/
@[path]
lemma proposition_34_blowup_properties
  [CommRing R]
  {𝔪 : Ideal R} :
-- imply
  Nonempty (tangentConeScheme 𝔪 ≅ exceptionalFiberScheme 𝔪) ∧ (scaleOnGraded 𝔪 1 = RingHom.id _) ∧ (∀ c₁ c₂ : R, scaleOnGraded 𝔪 (c₁ * c₂) = (scaleOnGraded 𝔪 c₁).comp (scaleOnGraded 𝔪 c₂)) :=
-- proof
  ⟨⟨tangentCone_isoExceptionalFiber 𝔪⟩,
    scaleOnGraded_one 𝔪,
    scaleOnGraded_comp 𝔪⟩
/-- Proposition 34 (corollary): the blowup is an isomorphism away from the centre `V(I)`. -/
end Prop34Blowup
namespace Prop38TangentCone
open Prop34Blowup in
/-- Proposition 38: for a regular local ring, the associated graded ring is isomorphic
to the symmetric algebra of the cotangent space over the residue field. -/
end Prop38TangentCone


/--
[scaleAlgHom_mem_reesAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean)
-/
@[path]
private lemma scaleAlgHom_mem_reesAlgebra_eq
  [CommRing R]
  {I : Ideal R}
  {c : R}
  {f : R[X]}
-- given
  (hf : f ∈ reesAlgebra I) :
-- imply
  (scaleAlgHom c : R[X] →ₐ[R] R[X]) f ∈ reesAlgebra I := by
-- proof
  apply Prop34Blowup.scaleAlgHom_mem_reesAlgebra I c f hf

/--
[scaleOnRees_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean)
-/
@[path]
private lemma scaleOnRees_algebraMap_eq
  [CommRing R]
  {I : Ideal R}
  {c : R}
  {r : R} :
-- imply
  scaleOnRees I c (algebraMap R (reesAlgebra I) r) = algebraMap R (reesAlgebra I) r := by
-- proof
  apply Prop34Blowup.scaleOnRees_algebraMap I c r

/--
[reesIdealFromBase_le_comap_scaleOnRees](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean)
-/
@[path]
private lemma reesIdealFromBase_le_comap_scaleOnRees_eq
  [CommRing R]
  {I : Ideal R}
  {c : R} :
-- imply
  reesIdealFromBase I ≤ (reesIdealFromBase I).comap (scaleOnRees I c) := by
-- proof
  apply Prop34Blowup.reesIdealFromBase_le_comap_scaleOnRees I c


-- created on 2026-10-23
