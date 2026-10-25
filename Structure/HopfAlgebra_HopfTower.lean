import Mathlib
import Instance.HopfAlgebra_HopfKerHopf
import Instance.HopfAlgebra_HopfTower
import Class.HopfAlgebra_HopfTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open Coalgebra WithConv

universe u v w x

namespace HopfAlgebra

namespace IsHopfTower

variable (k : Type u) (A : Type v) (C : Type w) [CommRing k] [CommRing A] [CommRing C]
    [HopfAlgebra k A] [HopfAlgebra k C] [Algebra A C] [IsScalarTower k A C]

variable [IsHopfTower k A C]


variable {k A C} in
omit [IsHopfTower k A C] in


end IsHopfTower

section augIdeal

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [HopfAlgebra k A]


variable {A} in

variable {A} in


end augIdeal

structure IsHopfSubalgebra (k : Type u) {H : Type v} [CommRing k] [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H) : Prop where
  comul_mem : ∀ x ∈ K, comul (R := k) x ∈
    Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}
  antipode_mem : ∀ x ∈ K, antipode k x ∈ K

namespace IsHopfSubalgebra

variable {k : Type u} {H : Type v} [CommRing k] [CommRing H] [HopfAlgebra k H]
variable {K : Subalgebra k H}


variable [Module.Flat k H] [Module.Flat k ↥K]


variable (hK : IsHopfSubalgebra k K)
include hK


end IsHopfSubalgebra

namespace HopfTower

section AntipodeAlgHom
variable (k : Type u) (C : Type v) [CommRing k] [CommRing C] [HopfAlgebra k C]


variable {k C}
variable {L : Type w} [CommRing L] [Algebra k L]


end AntipodeAlgHom

section Galois

variable (k : Type u) (A : Type v) (B : Type w) (C : Type x)
  [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [IsScalarTower k A B] [IsScalarTower k B C] [IsScalarTower k A C]
  [IsHopfTower k A B] [IsHopfTower k B C] [IsHopfTower k A C]


end Galois

section Naturality

universe y

variable (k : Type u) (A : Type v) (B : Type w) (B' : Type y) (C : Type x)
  [CommRing k] [CommRing A] [CommRing B] [CommRing B'] [CommRing C]
  [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k B'] [HopfAlgebra k C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [Algebra A B'] [Algebra B' C] [IsScalarTower A B' C]
  [Algebra B B'] [IsScalarTower A B B'] [IsScalarTower B B' C]
  [IsScalarTower k A B] [IsScalarTower k B C] [IsScalarTower k A C]
  [IsScalarTower k A B'] [IsScalarTower k B' C] [IsScalarTower k B B']
  [IsHopfTower k A B] [IsHopfTower k B C] [IsHopfTower k A C]
  [IsHopfTower k A B'] [IsHopfTower k B' C] [IsHopfTower k B B']

omit [HopfAlgebra k B] [HopfAlgebra k B'] [Algebra B C] [IsScalarTower A B C] [Algebra B' C]
  [IsScalarTower A B' C] [IsScalarTower B B' C] [IsScalarTower k A B] [IsScalarTower k B C]
  [IsScalarTower k A B'] [IsScalarTower k B' C] [IsScalarTower k B B'] [IsHopfTower k A B]
  [IsHopfTower k B C] [IsHopfTower k A B'] [IsHopfTower k B' C] [IsHopfTower k B B']
  [HopfAlgebra k C] [Algebra A C] [IsScalarTower k A C] [IsHopfTower k A C] in


end Naturality

section Translate

variable (k : Type u) (C : Type v) [CommRing k] [CommRing C] [HopfAlgebra k C]


variable {k C}


variable (k C) in


end Translate

section TranslateTower

variable (k : Type u) (A : Type v) (C : Type w) [CommRing k] [CommRing A] [CommRing C]
    [HopfAlgebra k A] [HopfAlgebra k C] [Algebra A C] [IsScalarTower k A C]


end TranslateTower

end HopfTower

end HopfAlgebra
