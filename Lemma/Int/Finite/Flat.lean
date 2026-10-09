import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[HopfAlgebra_finiteFlat_tensorProduct](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_finiteFlat_tensorProduct.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B] [Module.Finite R A] [Module.Flat R A] [Module.Finite R B] [Module.Flat R B] :
-- imply
  Module.Finite R (A ⊗[R] B) ∧ Module.Flat R (A ⊗[R] B) :=
-- proof
  ⟨inferInstance, inferInstance⟩


-- created on 2026-10-03
