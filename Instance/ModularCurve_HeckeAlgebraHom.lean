-- Carved from Lemma/Definitions/Def_ModularCurve_HeckeAlgebraHom.lean: instance decls only.
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Finiteness

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace ModularCurve.Period

section FGInfrastructure

instance instGroupFG_SL2Z : Group.FG SL(2, ℤ) :=
  ⟨⟨{ModularGroup.S, ModularGroup.T}, by
    simp only [Finset.coe_insert, Finset.coe_singleton]
    exact SpecialLinearGroup.SL2Z_generators⟩⟩

instance instGroupFG_Gamma0 (N : ℕ) [NeZero N] : Group.FG (Gamma0 N) := inferInstance

variable {G : Type*} [Group G]


instance instIsNoetherian_addHom_int (N : ℕ) [NeZero N] :
    IsNoetherian ℤ (Additive (Gamma0 N) →+ ℤ) :=
  have := addHom_int_moduleFinite (G := (Gamma0 N))
  inferInstance


end FGInfrastructure


section ParabolicFiniteness

variable (N : ℕ) [NeZero N]

instance parabolicHoms_int_moduleFinite :
    Module.Finite ℤ (parabolicHoms ℤ (Gamma0 N) ℤ) :=
  Module.Finite.of_injective (parabolicHoms ℤ (Gamma0 N) ℤ).subtype
    (parabolicHoms ℤ (Gamma0 N) ℤ).injective_subtype

end ParabolicFiniteness

end ModularCurve.Period
