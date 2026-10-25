-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_RelativeGroupLawEndDegree.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicGeometry.RelativeGroupLaw
import Lemma.GoodReductionJacobian.RelativeGroupLawKernel
import Lemma.AlgebraicGeometry.NeronModelEndomorphismExtension
import Lemma.AlgebraicGeometry.RelativeGroupLawEndDegree

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra


namespace GoodReductionJacobian
namespace RelativeGroupLaw


section Field

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

instance isIso_endKerStr_schemeHomOverId (G : RelativeGroupLaw K f) :
    IsIso (G.endKerStr (schemeHomOverId f)) := by
  change IsIso (pullback.snd (𝟙 A) (G.one (𝟙 (Spec (CommRingCat.of K)))).1)
  infer_instance

end Field

end RelativeGroupLaw
end GoodReductionJacobian

end
