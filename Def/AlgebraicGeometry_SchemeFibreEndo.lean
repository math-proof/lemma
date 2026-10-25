import Mathlib.AlgebraicGeometry.ResidueField

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

def schemeFibreEndo {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X) (hcomm : h ≫ f = f)
    (s : S) :
    Limits.pullback f (S.fromSpecResidueField s)
      ⟶ Limits.pullback f (S.fromSpecResidueField s) :=
  Limits.pullback.lift (Limits.pullback.fst _ _ ≫ h) (Limits.pullback.snd _ _)
    (by rw [Category.assoc, hcomm, Limits.pullback.condition])

end AlgebraicGeometry

end
