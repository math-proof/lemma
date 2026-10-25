import Mathlib

set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace FreyPackage.ModMCarrier

section LatticeRed
variable (k : Type*) [Field k] {W W' : Type*} [AddCommGroup W] [AddCommGroup W']
  [Module ℂ W] [Module ℂ W'] (L : Submodule ℤ W) (L' : Submodule ℤ W')

abbrev latticeRed : Type _ := k ⊗[ℤ] ↥L

end LatticeRed

end FreyPackage.ModMCarrier
