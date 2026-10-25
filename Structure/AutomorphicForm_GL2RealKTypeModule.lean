import Mathlib
import Def.AutomorphicForm_GL2RealKTypeModule

set_option autoImplicit false

namespace AutomorphicForm

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

structure IsGL2RealKTypeModule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) : Prop where
  isInternal : DirectSum.IsInternal wt
  map_raise_le : ∀ n : ℤ, (wt n).map E ≤ wt (n + 2)
  map_lower_le : ∀ n : ℤ, (wt n).map L ≤ wt (n - 2)
  raise_lower_sub : ∀ (n : ℤ) (v : M), v ∈ wt n → E (L v) - L (E v) = (n : ℂ) • v
  map_refl_le : ∀ n : ℤ, (wt n).map ε ≤ wt (-n)
  refl_comp_refl : ε ∘ₗ ε = LinearMap.id
  refl_comp_raise : ε ∘ₗ E = L ∘ₗ ε


end AutomorphicForm
