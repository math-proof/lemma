/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminant.lean -/

import Def.NumberTheory.NumberField.LatticeDiscriminant
import Lemma.Nat.NumberField.LatticeDiscriminant
import Def.NumberTheory.NumberField.ExtensionDiscriminant
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

/-- Membership in imageOfB is membership in the range of the algebra map from B to L. -/
theorem mem_imageOfB {x : L} :
    x ∈ imageOfB A L B ↔ ∃ b : B, algebraMap B L b = x := by
  simp only [imageOfB, Subalgebra.mem_toSubmodule, AlgHom.mem_range,
    IsScalarTower.coe_toAlgHom']

end ImageOfB
