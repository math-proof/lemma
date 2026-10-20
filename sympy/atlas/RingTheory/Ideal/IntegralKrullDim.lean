/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Ideal/IntegralKrullDim.lean -/

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-- Krull dimension cannot increase along an integral extension of commutative rings.

This is the dimension consequence of strict contraction of prime ideals
(`Ideal.IsIntegral.comap_lt_comap`): contraction gives a strictly monotone map
`PrimeSpectrum B → PrimeSpectrum A`, hence the inequality of Krull dimensions. -/
theorem ringKrullDim_le_of_integral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] : ringKrullDim B ≤ ringKrullDim A :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B))
    (fun _ _ h => Ideal.IsIntegral.under_lt_under h)
