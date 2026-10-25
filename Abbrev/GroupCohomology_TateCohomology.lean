import Mathlib

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)


abbrev tateH0 : Type _ := ρ.invariants ⧸ LinearMap.range ρ.normBar

abbrev tateHneg1 : Type _ := LinearMap.ker ρ.normBar

end Representation

namespace Rep

section lowDegrees

variable {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]

abbrev tateH0 (A : Rep.{w} k G) : Type w := A.ρ.tateH0

abbrev tateHneg1 (A : Rep.{w} k G) : Type w := A.ρ.tateHneg1

section maps

variable {A B C : Rep.{w} k G} (φ : A ⟶ B) (ψ : B ⟶ C)

noncomputable abbrev invariantsMap : A.ρ.invariants →ₗ[k] B.ρ.invariants :=
  ((Rep.invariantsFunctor k G).map φ).hom

omit [Fintype G] in

noncomputable abbrev coinvariantsMap : A.ρ.Coinvariants →ₗ[k] B.ρ.Coinvariants :=
  ((Rep.coinvariantsFunctor k G).map φ).hom

omit [Fintype G] in


end maps

end lowDegrees

section graded

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]


end graded

end Rep
