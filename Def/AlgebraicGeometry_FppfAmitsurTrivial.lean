import Def.Algebra_DescentCofaces

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

open CategoryTheory Opposite Algebra.DescentCofaces

def FppfAmitsurTrivial (F : Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (A : Type) [CommRing A] : Prop :=
  ∀ c : ToType (F.obj.obj (op (Spec (R₂ ℤ A)))),
    F.obj.map (Spec.map (c₁₂ ℤ A)).op c + F.obj.map (Spec.map (c₂₃ ℤ A)).op c =
        F.obj.map (Spec.map (c₁₃ ℤ A)).op c →
      ∃ b : ToType (F.obj.obj (op (Spec (CommRingCat.of A)))),
        c = F.obj.map (Spec.map (i₁ ℤ A)).op b - F.obj.map (Spec.map (i₂ ℤ A)).op b

end AlgebraicGeometry.Scheme
