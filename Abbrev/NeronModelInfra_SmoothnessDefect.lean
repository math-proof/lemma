import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace NeronModelInfra

abbrev pointAlgebra {X : Scheme.{u}} {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ X) :
    Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' :=
  (Scheme.stalkClosedPointTo a).hom.toAlgebra

section Gate

variable (R : Type u) [CommRing R]

end Gate

end NeronModelInfra

end

/--
info: 'NeronModelInfra.smoothnessDefect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.smoothnessDefect

/--
info: 'NeronModelInfra.smoothnessDefect_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.smoothnessDefect_id
