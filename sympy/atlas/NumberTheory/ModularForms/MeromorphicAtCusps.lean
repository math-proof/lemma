/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/MeromorphicAtCusps.lean -/

import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Meromorphic functions at modular cusps
-/

open scoped UpperHalfPlane MatrixGroups

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

theorem IsMeromorphicAtCusps.at_infty {f : ℍ → ℂ} (hf : IsMeromorphicAtCusps f) :
    IsMeromorphicAtInfty f := by
  simpa using hf 1

end ModularFunction
