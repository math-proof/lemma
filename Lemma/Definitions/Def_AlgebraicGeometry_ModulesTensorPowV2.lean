import Mathlib
import Lemma.Definitions.Def_SheafOfModules_MonoidalV2

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

def tensorPow (L : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => tensorPow L n ⊗ L

@[simp] theorem tensorPow_zero (L : X.Modules) : L.tensorPow 0 = 𝟙_ X.Modules := rfl

@[simp] theorem tensorPow_succ (L : X.Modules) (n : ℕ) : L.tensorPow (n + 1) = L.tensorPow n ⊗ L := rfl

def tensorPowOneIso (L : X.Modules) : L.tensorPow 1 ≅ L := λ_ L

end AlgebraicGeometry.Scheme.Modules

end
