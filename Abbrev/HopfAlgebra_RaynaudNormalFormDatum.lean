import Mathlib
import Structure.HopfAlgebra_FVectStructure
import Class.HopfAlgebra_HopfTower
import Instance.Compat_Mathlib430
import Structure.HopfAlgebra_RaynaudNormalFormDatum

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

section Cotangent

variable (R : Type*) [CommRing R] (B : Type*) [CommRing B] [HopfAlgebra R B]

abbrev Cot : Type _ := (augIdeal R B).Cotangent

end Cotangent

namespace FVect

variable (R' : Type*) [CommRing R'] (p r : ℕ) [NeZero r] (F : Type*) [Field F] [Fintype F]
  (B : Type*) [CommRing B] [HopfAlgebra R' B] (fv : FVectStructure F R' B) (χ : Fˣ →* R'ˣ)


namespace NormalFormDatum

variable {R' p r F B fv χ}
variable (D : NormalFormDatum R' p r F B fv χ)

end NormalFormDatum

variable (R : Type*) [CommRing R] [Algebra R R'] (Γ : Type*) [Group Γ] [MulSemiringAction Γ R']


namespace DescentDatum

variable {R' p r F B fv χ R Γ}


end DescentDatum

end FVect

end HopfAlgebra

end
