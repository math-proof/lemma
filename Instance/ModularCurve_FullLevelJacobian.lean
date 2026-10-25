-- Carved from Lemma/Definitions/Def_ModularCurve_FullLevelJacobian.lean: instance decls only.
import Lemma.ModularCurve.XHOperators
import Instance.CuspidalType_IsCuspidalOfType
import Def.HeckeGalois_EichlerShimura
import Lemma.ModularCurve.FullLevelJacobian

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve.FullLevel


section Idx

variable (q : ℕ)

instance : Fintype (Idx q) := inferInstanceAs (Fintype ↥(primitiveRoots q (AlgebraicClosure ℚ)))

instance : DecidableEq (Idx q) := Classical.decEq _

variable {q}

variable [Fact q.Prime]

instance : MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Idx q) where
  smul σ ζ := Idx.mk (σ ζ.val) (ζ.isPrimitiveRoot.map_of_injective σ.injective)
  one_smul _ := Idx.ext rfl
  mul_smul _ _ _ := Idx.ext rfl

end Idx

section Carrier

variable (q : ℕ) (M' : ℕ)

instance : AddCommGroup (Jac q M') := inferInstanceAs (AddCommGroup (Idx q → jacComp q M'))

variable {q M'}

end Carrier


end ModularCurve.FullLevel

end
