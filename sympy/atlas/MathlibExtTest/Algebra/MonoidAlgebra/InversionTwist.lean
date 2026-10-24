/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/MonoidAlgebra/InversionTwist.lean -/


import sympy.atlas.Algebra.MonoidAlgebra.InversionTwist

open GroupRing

variable (R G : Type*) [CommRing R] [CommGroup G]

example (g : G) (r : R) :
    inversion R G (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r := by
  simp

example (x : MonoidAlgebra R G) : inversion R G (inversion R G x) = x := by
  simp

variable {R G} {A : Type*} [AddCommGroup A] [Module (MonoidAlgebra R G) A]

example (r : MonoidAlgebra R G) (a : InversionTwist A) :
    (r • a).val = inversion R G r • a.val := by
  simp

example (a : InversionTwist (InversionTwist A)) :
    InversionTwist.twistTwistEquiv (R := R) (G := G) a = a.val.val :=
  rfl

example (r : MonoidAlgebra R G) (a : InversionTwist (InversionTwist A)) :
    InversionTwist.twistTwistEquiv (R := R) (G := G) (r • a) =
      r • InversionTwist.twistTwistEquiv (R := R) (G := G) a := by
  exact LinearEquiv.map_smul _ r a
