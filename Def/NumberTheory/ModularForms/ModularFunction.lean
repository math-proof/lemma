/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/ModularFunction.lean -/

import Def.NumberTheory.ModularForms.MeromorphicAtCusps
import Lemma.Nat.ModularForms.MeromorphicAtCusps
open scoped UpperHalfPlane MatrixGroups

/-!
# Modular functions

This module defines modular functions on the upper half-plane for an
arbitrary subgroup of `SL(2, ℤ)`: meromorphic functions invariant under
the group action and meromorphic at the cusps.
-/


namespace ModularFunction

/-- A function on `ℍ` is meromorphic if it extends to a function
meromorphic on the upper half-plane viewed as a subset of `ℂ`. -/
def IsMeromorphicOnH (f : ℍ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, MeromorphicOn g UpperHalfPlane.upperHalfPlaneSet ∧
    ∀ τ : ℍ, g (τ : ℂ) = f τ

/-- A function on `ℍ` is invariant under `Γ` if it is constant on
each `Γ`-orbit for the Möbius action. -/
def IsInvariantUnder (f : ℍ → ℂ) (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∀ (γ : SL(2, ℤ)), γ ∈ Γ → ∀ τ : ℍ, f (γ • τ) = f τ

end ModularFunction
