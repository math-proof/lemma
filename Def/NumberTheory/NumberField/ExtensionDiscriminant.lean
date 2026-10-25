/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminant.lean -/

import Def.NumberTheory.NumberField.LatticeDiscriminant
import Lemma.Nat.NumberField.LatticeDiscriminant
set_option autoImplicit false

universe u

/-!
# Extension discriminants

For a tower A to B to L, imageOfB is the image of B in L as an A-submodule. The extension
discriminant is the lattice discriminant of that submodule.

The result is represented as an A-submodule of K, not literally as an Ideal A. Showing that it
comes from an integral ideal requires additional hypotheses.
-/


section ImageOfB

variable (A : Type*) (L : Type u) (B : Type*)
  [CommRing A] [CommRing B] [Field L]
  [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]

/-- The image of B in L, regarded as an A-submodule of L. -/
def imageOfB : Submodule A L :=
  Subalgebra.toSubmodule (IsScalarTower.toAlgHom A B L).range

end ImageOfB
