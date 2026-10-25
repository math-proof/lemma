import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option autoImplicit false

open LinearMap
open scoped TensorProduct

namespace Representation

universe u

variable {k : Type*} [Field k] {G : Type*} [Group G] {W : Type*} [AddCommMonoid W] [Module k W]

class IsAbsolutelyIrreducible (ρ : Representation k G W) : Prop where
  absolutelyIrreducible :
    ∀ (k' : Type u) [Field k'] [Algebra k k'],
      IsIrreducible
        { toFun := fun g => LinearMap.baseChange k' (ρ g)
          map_one' := by aesop
          map_mul' := by aesop : Representation k' G (k' ⊗[k] W) }

end Representation
