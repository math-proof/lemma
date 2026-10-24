/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Spectrum/Prime/GroupAction.lean -/


import Lemma.Int.Spectrum.Prime.GroupAction

/-!
# Tests for group actions on prime spectra
-/


open scoped Pointwise

namespace N150Test

example {G R : Type*} [Group G] [CommSemiring R] [MulSemiringAction G R] :
    MulAction G (PrimeSpectrum R) :=
  inferInstance

example {G R : Type*} [Group G] [CommSemiring R] [MulSemiringAction G R]
    (g : G) (p : PrimeSpectrum R) :
    (g • p).asIdeal = g • p.asIdeal :=
  PrimeSpectrum.smul_asIdeal g p

example {G R : Type*} [Group G] [CommSemiring R] [MulSemiringAction G R]
    (p : PrimeSpectrum R) : (1 : G) • p = p :=
  one_smul _ _

example {G R : Type*} [Group G] [CommSemiring R] [MulSemiringAction G R]
    (g h : G) (p : PrimeSpectrum R) :
    (g * h) • p = g • h • p :=
  mul_smul _ _ _

end N150Test
