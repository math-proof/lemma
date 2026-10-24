import Mathlib
import Lemma.Definitions.Def_ModularCurve_X0

noncomputable section

open IntermediateField

namespace ModularCurve

section Tower

variable (N : ℕ) [NeZero N]

def jAdjoinRingHom : ℚ⟮jq⟯ →+* modularFunctionField N where
  toFun x := ⟨(x : LaurentSeries ℚ), adjoin_jq_le N x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[reducible] def algebraIntPolyModularFunctionField : Algebra (Polynomial ℤ) (modularFunctionField N) :=
  ((jAdjoinRingHom N).comp evalAtJGen).toAlgebra

attribute [local instance] algebraIntPolyModularFunctionField

abbrev routeBCoordRing : Subalgebra (Polynomial ℤ) (modularFunctionField N) :=
  integralClosure (Polynomial ℤ) (modularFunctionField N)

def routeBJValue {N : ℕ} [NeZero N] {L : Type*} [CommRing L] (φ : ↥(routeBCoordRing N) →+* L) : L :=
  φ ⟨algebraMap (Polynomial ℤ) ↥(modularFunctionField N) Polynomial.X, Subalgebra.algebraMap_mem _ _⟩

end Tower

end ModularCurve

end
