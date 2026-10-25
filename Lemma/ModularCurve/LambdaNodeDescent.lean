import Mathlib
import Lemma.ModularCurve.LambdaNodeLocalized
import Def.ModularCurve_NodeDescent
import Def.ModularCurve_LambdaNodeDescent

set_option autoImplicit false

namespace ModularCurve
namespace LambdaNodeLocalized
noncomputable section

open NodeLocalized


theorem mem_lambdaIntegralClosure (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) {x : LaurentSeries (AlgebraicClosure ℚ)} :
    x ∈ lambdaIntegralClosure N A K ↔ x ∈ lambdaFieldOver N K ∧ IsIntegral (lambdaRing A K) x :=
  Iff.rfl

theorem lambdaModC_mem_lambdaFieldOver (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    lambdaModC (AlgebraicClosure ℚ) ∈ lambdaFieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem lambdaNModC_mem_lambdaFieldOver (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    lambdaNModC (AlgebraicClosure ℚ) N ∈ lambdaFieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end

end LambdaNodeLocalized

end ModularCurve
