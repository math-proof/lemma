-- Carved from Lemma/Definitions/Def_HopfAlgebra_CharacterClosure.lean: instance decls only.
import Mathlib
import Instance.HopfAlgebra_CartierDual
import Instance.FiniteFlat_SchematicClosure

set_option autoImplicit false

open scoped TensorProduct


namespace CartierDual

section BaseChange

universe u v w

variable (O : Type u) [CommRing O] (F : Type v) [CommRing F] [Algebra O F]
variable (A : Type w) [CommRing A] [Bialgebra O A]

noncomputable instance instModuleRestrictBaseChange : Module O (CartierDual F (F ⊗[O] A)) :=
  Module.compHom (CartierDual F (F ⊗[O] A)) (algebraMap O F)

instance instIsScalarTowerRestrictBaseChange : IsScalarTower O F (CartierDual F (F ⊗[O] A)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

noncomputable instance instRingBaseChangeDual : Ring (F ⊗[O] CartierDual O A) := Algebra.TensorProduct.instRing

noncomputable instance instAlgebraBaseChangeDual : Algebra F (F ⊗[O] CartierDual O A) :=
  Algebra.TensorProduct.leftAlgebra

variable {O F A}

end BaseChange

end CartierDual

