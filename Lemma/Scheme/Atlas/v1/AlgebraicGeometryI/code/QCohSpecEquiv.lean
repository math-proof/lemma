import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.QCohSpecEquiv
open AlgebraicGeometry CategoryTheory


/--
[tilde_isQuasicoherent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohSpecEquiv.lean)
-/
@[path]
lemma tilde_isQuasicoherent
  {R : CommRingCat.{u}}
  {M : ModuleCat.{u} R} :
-- imply
  (tilde M).IsQuasicoherent :=
-- proof
  inferInstance

/--
[tilde_essImage_iff_isIso_counit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohSpecEquiv.lean)
-/
@[path]
lemma tilde_essImage_iff_isIso_counit
  {R : CommRingCat.{u}}
  {M : (Spec (.of R)).Modules} :
-- imply
  (tilde.functor R).essImage M ↔ IsIso M.fromTildeΓ :=
-- proof
  isIso_fromTildeΓ_iff.symm

/--
[tilde_counit_isIso_of_presentation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohSpecEquiv.lean)
-/
@[path]
lemma tilde_counit_isIso_of_presentation
  {R : CommRingCat.{u}}
  {M : (Spec R).Modules}
  {P : M.Presentation} :
-- imply
  IsIso M.fromTildeΓ :=
-- proof
  isIso_fromTildeΓ_of_presentation M P


-- created on 2026-10-23
