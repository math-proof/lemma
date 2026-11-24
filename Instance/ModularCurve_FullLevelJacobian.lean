module
public import Theorem.UpperHalfPlane.XHOperators
public import Instance.CuspidalType_IsCuspidalOfType
public import Def.HeckeGalois_EichlerShimura
public import Theorem.Matrix.FullLevelJacobian
public import Def.ModularCurve_FullLevelJacobian
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_ModularCurve_FullLevelJacobian.lean: instance decls only.

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
