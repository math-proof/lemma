/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/MeromorphicAtCusps.lean -/

module

public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Meromorphic.Basic

@[expose] public section

open scoped UpperHalfPlane MatrixGroups

/-!
# Meromorphic functions at modular cusps
-/


namespace ModularFunction

/-- A function on the upper half-plane is meromorphic at infinity when it is eventually the
pullback, along a positive-period `q`-parameter, of a function meromorphic at zero. -/
def IsMeromorphicAtInfty (f : ℍ → ℂ) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (g : ℂ → ℂ), MeromorphicAt g 0 ∧
    ∀ᶠ τ in UpperHalfPlane.atImInfty,
      f τ = g (Function.Periodic.qParam (N : ℝ) (τ : ℂ))

/-- A function is meromorphic at the cusps when every `SL(2, ℤ)`-translate is meromorphic at
infinity. -/
def IsMeromorphicAtCusps (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), IsMeromorphicAtInfty (fun τ ↦ f (γ • τ))

end ModularFunction
