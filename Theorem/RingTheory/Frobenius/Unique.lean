/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Unique.lean -/
module

public import Mathlib.RingTheory.Frobenius

public section

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  {Q : Ideal S} {σ σ' : G}


namespace IsArithFrobAt
end IsArithFrobAt
