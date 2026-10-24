import Mathlib
import Lemma.Definitions.Def_ModularCurve_JHNodeDepth

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace ModularCurve
namespace JHPlaceSpecialization

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
variable {A : ValuationSubring (AlgebraicClosure ℚ)}
variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

def AnnulusDepthLawInf (P : JHPlaceSpecialization p M H hpM A)
    (α : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral)
    (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (depth : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℕ) : Prop :=
  ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), P.reduceFst α hα V = s.1 →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) →
    A.valuation (V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An.modulus : ↥A) : AlgebraicClosure ℚ)) * An.param⁻¹)) =
      A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ depth V

end JHPlaceSpecialization
end ModularCurve

end
