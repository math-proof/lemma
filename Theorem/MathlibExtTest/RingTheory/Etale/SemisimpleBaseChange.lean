/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Etale/SemisimpleBaseChange.lean -/


import Lemma.Int.Etale.SemisimpleBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
open scoped TensorProduct

variable {K Ω B : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  [CommRing B] [Algebra K B] [Module.Finite K B]


-- Generalized theorem over an arbitrary algebraically closed extension.
example (h : IsSemisimpleRing (Ω ⊗[K] B)) : Algebra.Etale K B :=
  Algebra.Etale.of_isSemisimpleRing_tensorProduct h

-- ATLAS input orientation, transported across `comm` to the new theorem.
example (h : IsSemisimpleRing (B ⊗[K] AlgebraicClosure K)) :
    Algebra.Etale K B := by
  have : IsSemisimpleRing (B ⊗[K] AlgebraicClosure K) := h
  have : IsSemisimpleRing (AlgebraicClosure K ⊗[K] B) :=
    (Algebra.TensorProduct.comm K B (AlgebraicClosure K)).toRingEquiv.isSemisimpleRing
  exact Algebra.Etale.of_isSemisimpleRing_tensorProduct
    (Ω := AlgebraicClosure K) inferInstance

