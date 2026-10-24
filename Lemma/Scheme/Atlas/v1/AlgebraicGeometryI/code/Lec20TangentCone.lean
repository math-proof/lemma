import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone
open Polynomial Lec20TangentCone


namespace Lec20TangentCone

/--
[scaleAlgHom_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean)
-/
@[path]
lemma scaleAlgHom_one
  {R : Type u}
  [CommRing R] :
-- imply
  scaleAlgHom (1 : R) = AlgHom.id R R[X] := by
-- proof
  ext; unfold scaleAlgHom; simp [map_one, one_mul]

end Lec20TangentCone

namespace Lec20TangentCone

/--
[scaleAlgHom_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean)
-/
@[path]
lemma scaleAlgHom_comp
  {R : Type u}
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

end Lec20TangentCone

namespace Lec20TangentCone

/--
[tangentCone_isCone_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean)
-/
@[path]
lemma tangentCone_isCone_identity
  {R : Type u}
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

end Lec20TangentCone

namespace Lec20TangentCone

/--
[tangentCone_isCone_compose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean)
-/
@[path]
lemma tangentCone_isCone_compose
  {R : Type u}
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

end Lec20TangentCone

namespace Lec20TangentCone

/--
[tangentCone_over_closedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean)
-/
@[path]
lemma tangentCone_over_closedPoint
  {R : Type u}
  [CommRing R]
  {𝔪 : Ideal R} :
-- imply
  𝔪 ≤ RingHom.ker (ringHomToAssocGraded 𝔪) := by
-- proof
  intro r hr
  rw [RingHom.mem_ker]
  show (Ideal.Quotient.mk (reesIdealFromBase 𝔪)) ((algebraMap R (reesAlgebra 𝔪)) r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hr

end Lec20TangentCone

namespace Lec20TangentCone

/--
[reesToAssocGraded_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean)
-/
@[path]
lemma reesToAssocGraded_surjective
  {R : Type u}
  [CommRing R]
  {𝔪 : Ideal R} :
-- imply
  Function.Surjective (reesToAssocGraded 𝔪) :=
-- proof
  Ideal.Quotient.mk_surjective
/-- Proposition 38 (smooth case): At a smooth (regular) point, the associated graded ring
is isomorphic to the symmetric algebra on the cotangent space, so the tangent cone is the
linear tangent space `Sym(T*_x X)`. -/
section TangentSpace

end Lec20TangentCone

/--
[scaleAlgHom_mem_reesAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean)
-/
@[path]
private lemma scaleAlgHom_mem_reesAlgebra_eq
  {R : Type u}
  [CommRing R]
  {I : Ideal R}
  {c : R}
  {f : R[X]}
-- given
  (hf : f ∈ reesAlgebra I) :
-- imply
  (scaleAlgHom c : R[X] →ₐ[R] R[X]) f ∈ reesAlgebra I := by
-- proof
  apply Lec20TangentCone.scaleAlgHom_mem_reesAlgebra I c f hf

/--
[scaleOnRees_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean)
-/
@[path]
private lemma scaleOnRees_algebraMap_eq
  {R : Type u}
  [CommRing R]
  {I : Ideal R}
  {c : R}
  {r : R} :
-- imply
  scaleOnRees I c (algebraMap R (reesAlgebra I) r) = algebraMap R (reesAlgebra I) r := by
-- proof
  apply Lec20TangentCone.scaleOnRees_algebraMap I c r

/--
[reesIdealFromBase_le_comap_scaleOnRees](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean)
-/
@[path]
private lemma reesIdealFromBase_le_comap_scaleOnRees_eq
  {R : Type u}
  [CommRing R]
  {I : Ideal R}
  {c : R} :
-- imply
  reesIdealFromBase I ≤ (reesIdealFromBase I).comap (scaleOnRees I c) := by
-- proof
  apply Lec20TangentCone.reesIdealFromBase_le_comap_scaleOnRees I c


-- created on 2026-10-23
