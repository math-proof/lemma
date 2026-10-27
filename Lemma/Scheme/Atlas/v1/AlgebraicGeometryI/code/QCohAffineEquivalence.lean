import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.QCohAffineEquivalence.Part2
open CategoryTheory AlgebraicGeometry Proposition18


namespace Proposition18

/--
[tilde_isQuasicoherent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohAffineEquivalence.lean)
-/
@[path]
lemma tilde_isQuasicoherent
  {R : CommRingCat.{u}}
  {M : ModuleCat.{u} R} :
-- imply
  (tilde M).IsQuasicoherent :=
-- proof
  inferInstance

end Proposition18

namespace Proposition18

/--
[isQuasicoherent_of_mem_essImage_tilde](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohAffineEquivalence.lean)
-/
@[path]
lemma isQuasicoherent_of_mem_essImage_tilde
  {R : CommRingCat.{u}}
  {ℱ : (Spec R).Modules}
-- given
  (h : (tilde.functor R).essImage ℱ) :
-- imply
  ℱ.IsQuasicoherent := by
-- proof
  rw [← isIso_fromTildeΓ_iff] at h
  haveI := h
  exact ((presentationTilde.{u} (moduleSpecΓFunctor.obj ℱ)
    Set.univ (by simp) _ (Submodule.span_eq _)).of_isIso ℱ.fromTildeΓ).isQuasicoherent

end Proposition18


-- created on 2026-10-23
