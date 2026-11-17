-- Carved from Lemma/Definitions/Def_FiniteFlat_SchematicClosure.lean: instance decls only.

module

public import Mathlib

@[expose] public section

open scoped TensorProduct

section FlatClosure

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G] [Algebra R G]

instance : IsScalarTower R F (F ⊗[R] G) := IsScalarTower.of_algebraMap_eq fun _ => rfl

end FlatClosure
