import Mathlib

set_option autoImplicit false

namespace AutomorphicForm

variable {M : Type*} [AddCommGroup M] [Module ℂ M]


def IsGL2RealKTypeSubmodule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M)
    (W : Submodule ℂ M) : Prop :=
  W ≤ (⨆ n : ℤ, W ⊓ wt n) ∧ W.map E ≤ W ∧ W.map L ≤ W ∧ W.map ε ≤ W

def IsIrreducibleGL2RealKTypeModule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) : Prop :=
  (∃ v : M, v ≠ 0) ∧
    ∀ W : Submodule ℂ M, IsGL2RealKTypeSubmodule wt E L ε W → W = ⊥ ∨ W = ⊤

end AutomorphicForm
