import Mathlib
import Lemma.Definitions.Def_ModularCurve_LambdaNodeLocalized
import Lemma.Definitions.Def_ModularCurve_NodeDescent

set_option autoImplicit false

namespace ModularCurve
namespace LambdaNodeLocalized
noncomputable section

open NodeLocalized

def lambdaFieldOver (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subfield (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subfield.closure (Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring)
    ∪ {lambdaModC (AlgebraicClosure ℚ), lambdaNModC (AlgebraicClosure ℚ) N})

def lambdaRing (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subring.closure (Set.range (CharPReduction.constSeries (coeffSubring A K)) ∪ {lambdaModC (AlgebraicClosure ℚ)})

def lambdaIntegralClosure (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (LaurentSeries (AlgebraicClosure ℚ)) where
  carrier := {x | x ∈ lambdaFieldOver N K ∧ IsIntegral (lambdaRing A K) x}
  zero_mem' := ⟨zero_mem _, isIntegral_zero⟩
  one_mem' := ⟨one_mem _, isIntegral_one⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, hx.2.add hy.2⟩
  neg_mem' := fun hx => ⟨neg_mem hx.1, hx.2.neg⟩
  mul_mem' := fun hx hy => ⟨mul_mem hx.1 hy.1, hx.2.mul hy.2⟩

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
