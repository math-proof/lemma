import Mathlib
import Lemma.GroupCohomology.RepPi

set_option autoImplicit false

open NumberField

namespace NumberField.InfPlaceDecomp

section general
variable {K : Type*} [Field K]


end general

variable (E K : Type*) [Field E] [Field K] [Algebra E K] (w : InfinitePlace K)

abbrev decomp : Subgroup (K ≃ₐ[E] K) := MulAction.stabilizer (K ≃ₐ[E] K) w

variable {E K w}


noncomputable abbrev localUnits : Rep ℤ (decomp E K w) := Rep.ofMulDistribMulAction (decomp E K w) (w.Completion)ˣ

end NumberField.InfPlaceDecomp

namespace NumberField.ArchIdele

open scoped NumberField.InfPlaceDecomp

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]


noncomputable abbrev obj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepPi.obj (fibre E K)

end NumberField.ArchIdele
