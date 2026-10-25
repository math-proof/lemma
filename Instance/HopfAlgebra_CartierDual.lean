-- Carved from Lemma/Definitions/Def_HopfAlgebra_CartierDual.lean: instance decls only.
import Mathlib
import Lemma.HopfAlgebra.CartierDual

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open Coalgebra
open scoped TensorProduct

universe u v

namespace CartierDual


noncomputable section

section Instances

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

instance instAddCommGroup : AddCommGroup (CartierDual R A) :=
  inferInstanceAs (AddCommGroup (Module.Dual R A))

instance instModule : Module R (CartierDual R A) :=
  inferInstanceAs (Module R (Module.Dual R A))

instance instRing : Ring (CartierDual R A) :=
  { instAddCommGroup R A, dualConvRing R A with }

instance instCommRing [IsCocomm R A] : CommRing (CartierDual R A) :=
  { instRing R A with mul_comm := fun f g => (dualConvCommRing R A).mul_comm f g }

instance instAlgebra : Algebra R (CartierDual R A) :=
  { dualConvAlgebra R A with toSMul := (instModule R A).toDistribMulAction.toMulAction.toSMul }

instance instFunLike : FunLike (CartierDual R A) A R :=
  inferInstanceAs (FunLike (A →ₗ[R] R) A R)

instance instLinearMapClass : LinearMapClass (CartierDual R A) R A R :=
  inferInstanceAs (LinearMapClass (A →ₗ[R] R) R A R)

variable {R A}

variable (R A)
variable [Module.Finite R A] [Module.Free R A]

instance instModuleFinite : Module.Finite R (CartierDual R A) :=
  inferInstanceAs (Module.Finite R (Module.Dual R A))

instance instModuleFree : Module.Free R (CartierDual R A) :=
  inferInstanceAs (Module.Free R (Module.Dual R A))

instance instCoalgebra : Coalgebra R (CartierDual R A) := { dualCoalgebraOfFiniteFree R A with }

instance instBialgebra : Bialgebra R (CartierDual R A) :=
  { instAlgebra R A, instCoalgebra R A, dualBialgebraOfFiniteFree R A with }

instance instIsCocomm : IsCocomm R (CartierDual R A) :=
  ⟨(dualCoalgebraOfFiniteFree_isCocomm R A).comm_comp_comul⟩

variable {R A}

end Instances

section HopfInstance

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A]

instance instHopfAlgebra : HopfAlgebra R (CartierDual R A) :=
  { instBialgebra R A, dualHopfAlgebraOfFiniteFree R A with }

variable {R A}

end HopfInstance


end

end CartierDual

namespace MonoidAlgebra

instance instModuleFreeOfCartier {R : Type*} [CommSemiring R] {Γ : Type*} :
    Module.Free R (MonoidAlgebra R Γ) :=
  .of_equiv (MonoidAlgebra.coeffLinearEquiv R).symm

instance instModuleFiniteOfCartier {R : Type*} [CommSemiring R] {Γ : Type*} [Finite Γ] :
    Module.Finite R (MonoidAlgebra R Γ) :=
  .equiv (MonoidAlgebra.coeffLinearEquiv R).symm

end MonoidAlgebra

