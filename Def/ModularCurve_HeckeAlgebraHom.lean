module
public import Instance.Gamma0HeckeOperatorHom
public import Lemma.UpperHalfPlane.PeriodMap
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.GroupTheory.Schreier
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.GroupTheory.Finiteness
set_option autoImplicit false
open CongruenceSubgroup
open scoped MatrixGroups


public section

namespace ModularCurve.Period

section FGInfrastructure


noncomputable def evalGen (S : Set G) : (Additive G →+ ℤ) →ₗ[ℤ] (S → ℤ) where
  toFun φ s := φ (Additive.ofMul (s : G))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end FGInfrastructure

section Vocabulary

variable (N ℓ : ℕ) [NeZero ℓ]

noncomputable def heckeOperatorEndHom : Module.End ℤ (Additive (Gamma0 N) →+ ℤ) :=
  AddMonoidHom.toIntLinearMap (HeckeEis.heckeOperatorHom N ℓ ℤ)

variable [NeZero N] (S : Set ℕ)

noncomputable def heckeAlgebraHom :
    Subalgebra ℤ (Module.End ℤ (Additive (Gamma0 N) →+ ℤ)) :=
  Algebra.adjoin ℤ
    {T | ∃ (ℓ : ℕ) (_ : NeZero ℓ), ℓ.Prime ∧ ℓ ∉ S ∧ T = heckeOperatorEndHom N ℓ}

end Vocabulary

end ModularCurve.Period
