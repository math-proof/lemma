import Instance.CohCarrier_Level

set_option autoImplicit false

namespace CohCarrier

open CongruenceSubgroup
open scoped MatrixGroups

section RightCosets

variable {Γ : Type*} [Group Γ] (S : Subgroup Γ)

abbrev cls (g : Γ) : Quotient (QuotientGroup.rightRel S) := Quotient.mk _ g

end RightCosets

section Unipotent

end Unipotent

section CosetProjection

variable {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
variable (h : LevelLE M M' H H' 1) (ℓ : ℕ)

end CosetProjection

section LowerLeg

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (q : ℕ)

abbrev GammaHLower : Subgroup ↥(GammaH M H) := (Gamma0 (q * M)).subgroupOf (GammaH M H)

end LowerLeg

end CohCarrier
