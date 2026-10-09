import Mathlib
import sympy.Basic


/--
[RingHom_Flat_quotientMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_Flat_quotientMap.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S]
  {f : R →+* S}
  {I : Ideal R}
-- given
  (hf : f.Flat) :
-- imply
  (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).Flat := by
-- proof
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  have key : Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  exact RingHom.flat_algebraMap_iff.mpr key


-- created on 2026-10-03
