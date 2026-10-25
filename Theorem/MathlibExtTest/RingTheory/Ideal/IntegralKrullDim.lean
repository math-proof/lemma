/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Ideal/IntegralKrullDim.lean -/


import Lemma.Int.Ideal.IntegralKrullDim


-- Generic API example: the lemma applies to any integral extension.
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] : ringKrullDim B ≤ ringKrullDim A :=
  ringKrullDim_le_of_integral

-- Standard specialization: finite dimension bounds transfer along integral extensions.
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] {n : ℕ} (h : ringKrullDim A ≤ n) :
    ringKrullDim B ≤ n :=
  ringKrullDim_le_of_integral.trans h

