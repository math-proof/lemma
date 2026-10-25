import Mathlib
import Def.ModularCurve_NodeLocalized

set_option autoImplicit false

namespace ModularCurve
namespace NodeLocalized
noncomputable section

def coeffSubring (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (AlgebraicClosure ℚ) :=
  A.toSubring ⊓ K.toSubalgebra.toSubring

def redRestrict {k : Type*} [Field k] {A : ValuationSubring (AlgebraicClosure ℚ)} (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : coeffSubring A K →+* k :=
  red.comp (Subring.inclusion inf_le_left)

def fieldOver (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Subfield (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subfield.closure (Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring)
    ∪ {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N})

def jRing (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subring.closure (Set.range (CharPReduction.constSeries (coeffSubring A K)) ∪ {jqModC (AlgebraicClosure ℚ)})

def jIntegralClosure (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (LaurentSeries (AlgebraicClosure ℚ)) where
  carrier := {x | x ∈ fieldOver N K ∧ IsIntegral (jRing A K) x}
  zero_mem' := ⟨zero_mem _, isIntegral_zero⟩
  one_mem' := ⟨one_mem _, isIntegral_one⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, hx.2.add hy.2⟩
  neg_mem' := fun hx => ⟨neg_mem hx.1, hx.2.neg⟩
  mul_mem' := fun hx hy => ⟨mul_mem hx.1 hy.1, hx.2.mul hy.2⟩

end
end NodeLocalized
end ModularCurve
