import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Etale.SemisimpleBaseChange
open scoped TensorProduct


/--
[Algebra.Etale.of_isSemisimpleRing_tensorProduct](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Etale/SemisimpleBaseChange.lean)
-/
@[path]
private lemma Algebra_Etale_of_isSemisimpleRing_tensorProduct_eq
  [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [CommRing A] [Algebra K A] [Module.Finite K A]
-- given
  (h : IsSemisimpleRing (Ω ⊗[K] A)) :
-- imply
  Algebra.Etale K A := by
-- proof
  apply Algebra.Etale.of_isSemisimpleRing_tensorProduct h


-- created on 2026-10-20
