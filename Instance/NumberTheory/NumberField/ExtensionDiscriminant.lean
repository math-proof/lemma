/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminant.lean -/

import Def.NumberTheory.NumberField.LatticeDiscriminant
import Lemma.Nat.NumberField.LatticeDiscriminant
import Theorem.NumberTheory.NumberField.ExtensionDiscriminant
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

/-- The image of a finite A-module B is finite as an A-module. -/
instance imageOfB_finite [Module.Finite A B] :
    Module.Finite A ↥(imageOfB A L B) := by
  have heq : imageOfB A L B =
      (IsScalarTower.toAlgHom A B L).toLinearMap.range := by
    ext x
    constructor
    · intro hx
      rw [mem_imageOfB A L B] at hx
      rcases hx with ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact (mem_imageOfB A L B).mpr ⟨b, rfl⟩
  rw [heq]
  exact Module.Finite.range (IsScalarTower.toAlgHom A B L).toLinearMap

end ImageOfB
