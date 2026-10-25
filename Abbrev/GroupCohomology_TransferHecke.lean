import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.Index

set_option autoImplicit false

open groupCohomology

namespace HeckeCohomology

variable {k Γ : Type} [CommRing k] [Group Γ] (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) (A : Rep k Γ)

abbrev cls (g : Γ) : Quotient (QuotientGroup.rightRel S₂) := Quotient.mk _ g

end HeckeCohomology
