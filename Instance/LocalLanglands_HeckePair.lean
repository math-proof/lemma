-- Carved from Lemma/Definitions/Def_LocalLanglands_HeckePair.lean: instance decls only.
import Mathlib
import Instance.AbstractHeckeOperator
import Lemma.LocalLanglands.HeckePair

set_option autoImplicit false

open scoped Pointwise
open Function MulAction

namespace HeckePair

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
variable (R₀ : Type*) [CommRing R₀]

variable {U R₀}

instance : Mul (HeckeAlgebra U R₀) :=
  ⟨fun f₁ f₂ => ⟨conv f₁ f₂, isHeckeFun_conv f₁ f₂⟩⟩

instance : One (HeckeAlgebra U R₀) := ⟨heckeOne U R₀⟩

instance : Ring (HeckeAlgebra U R₀) where
  __ : AddCommGroup (HeckeAlgebra U R₀) := inferInstance
  mul := (· * ·)
  one := 1
  mul_assoc := HeckePair.mul_assoc
  one_mul := HeckePair.one_mul
  mul_one := HeckePair.mul_one
  left_distrib := HeckePair.mul_add
  right_distrib := fun f₁ f₂ g => HeckePair.add_mul f₁ f₂ g
  zero_mul := HeckePair.zero_mul
  mul_zero := HeckePair.mul_zero

instance : SMulCommClass R₀ (HeckeAlgebra U R₀) (HeckeAlgebra U R₀) :=
  ⟨fun r f g => (HeckePair.mul_smul_comm r f g).symm⟩

instance : IsScalarTower R₀ (HeckeAlgebra U R₀) (HeckeAlgebra U R₀) :=
  ⟨fun r f g => by rw [smul_eq_mul, smul_eq_mul, HeckePair.smul_mul]⟩

instance : Algebra R₀ (HeckeAlgebra U R₀) :=
  Algebra.ofModule HeckePair.smul_mul HeckePair.mul_smul_comm

end
end HeckePair
