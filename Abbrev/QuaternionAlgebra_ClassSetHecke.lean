import Mathlib
import Def.Submodule_FiniteAdeleBox
import Structure.QuaternionAlgebra_Order
import Def.QuaternionAlgebra_ReducedNorm

set_option autoImplicit false

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace QuaternionAlgebra

variable {a b : ℚ}

abbrev ClassSet (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Type :=
  DoubleCoset.Quotient
    (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range :
        Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (U : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)

namespace ClassSet

variable {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

variable (U) in

abbrev mk (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ClassSet U :=
  DoubleCoset.mk (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U x

end ClassSet

section HeckeKernel

end HeckeKernel

section Level

end Level

end QuaternionAlgebra

end
