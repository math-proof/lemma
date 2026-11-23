module

public import Mathlib
public import Instance.Deformations_ContinuousSMulDiscrete

@[expose] public section

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace IsArithFrobAt

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
variable {Q : Ideal S} {σ σ' : G}

variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable [IsTopologicalGroup G] [Algebra.IsInvariant R S G]
variable [ContinuousSMulDiscrete G S]

variable (R G Q)

noncomputable
def _root_.arithFrobAt' [Q.IsPrime] [Finite (R ⧸ Q.under R)] : G :=
  (exists_primesOver_isConj_of_profinite S G (Q.under R)).choose ⟨Q, ‹_›, ⟨rfl⟩⟩

end IsArithFrobAt

end

end
