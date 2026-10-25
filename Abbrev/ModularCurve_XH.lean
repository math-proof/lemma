import Mathlib
import Lemma.ModularCurve.X1
import Instance.CohCarrier_Level
import Instance.EllipticCurve_TateModule

set_option autoImplicit false

noncomputable section

open IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

section Groups

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)


end Groups

section FunctionField

variable (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ)


end FunctionField

section Jacobian

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

abbrev xHFunctionFieldBar :
    IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField M H)

abbrev JH : Type _ :=
  Pic0 (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)

example : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JH M H) :=
  inferInstance

example : DistribMulAction (AddMonoid.End (JH M H)) (JH M H) := inferInstance

theorem JH.torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) n) :
    JH.torsionGaloisRep M H n σ x = arithmeticGalois (xHFunctionField M H) σ • x :=
  rfl


abbrev JH.tateGaloisRep :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] (TateModule p (JH M H)) :=
  TateModule.rep p (JH M H) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

abbrev JH.tateEnd : AddMonoid.End (JH M H) →* Module.End ℤ_[p] (TateModule p (JH M H)) :=
  TateModule.rep p (JH M H) (AddMonoid.End (JH M H))


end Jacobian

end ModularCurve

end
