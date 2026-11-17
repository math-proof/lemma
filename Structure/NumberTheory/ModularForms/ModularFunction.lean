/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/ModularFunction.lean -/

module

public import Def.NumberTheory.ModularForms.MeromorphicAtCusps
public import Theorem.Nat.ModularForms.MeromorphicAtCusps
public import Def.NumberTheory.ModularForms.ModularFunction
public section

open scoped UpperHalfPlane MatrixGroups

open ModularFunction

/-!
# Modular functions

This module defines modular functions on the upper half-plane for an
arbitrary subgroup of `SL(2, ℤ)`: meromorphic functions invariant under
the group action and meromorphic at the cusps.
-/


/-- A modular function for `Γ`: meromorphic on `ℍ`, invariant under
`Γ`, and meromorphic at the cusps. No congruence hypothesis is
assumed on `Γ`. -/
structure IsModularFunction (f : ℍ → ℂ) (Γ : Subgroup SL(2, ℤ)) : Prop where
  meromorphicOnH : IsMeromorphicOnH f
  invariant : IsInvariantUnder f Γ
  meromorphicAtCusps : IsMeromorphicAtCusps f

