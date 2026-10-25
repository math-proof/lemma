import Instance.Gamma0HeckeOperatorHom
import Lemma.ModularCurve.PeriodMap
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Finiteness

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

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
