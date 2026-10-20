/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/ModularFunction.lean -/

import sympy.atlas.NumberTheory.ModularForms.MeromorphicAtCusps
/-!
# Modular functions

This module defines modular functions on the upper half-plane for an
arbitrary subgroup of `SL(2, ℤ)`: meromorphic functions invariant under
the group action and meromorphic at the cusps.
-/

open scoped UpperHalfPlane MatrixGroups

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

open ModularFunction

/-- A modular function for `Γ`: meromorphic on `ℍ`, invariant under
`Γ`, and meromorphic at the cusps. No congruence hypothesis is
assumed on `Γ`. -/
structure IsModularFunction (f : ℍ → ℂ) (Γ : Subgroup SL(2, ℤ)) : Prop where
  meromorphicOnH : IsMeromorphicOnH f
  invariant : IsInvariantUnder f Γ
  meromorphicAtCusps : IsMeromorphicAtCusps f
