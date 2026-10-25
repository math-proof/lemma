import Instance.CerednikDrinfeld_DrinfeldUpperHalfPlane
import Instance.CerednikDrinfeld_MumfordQuotient
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open Filter CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace CerednikDrinfeld.Omega

variable (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]


variable {K₀ K} (ϖ : PseudoUniformizer K₀ K)


namespace RatPair

end RatPair

section Hol

variable (K)

abbrev vRestrict : Valuation K (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v (R := K)))) := (Valued.v (R := K)).restrict

end Hol

section Actions

variable [DecidableEq K]

section Stab

local notation "𝔭" => Valued.v (algebraMap K₀ K ϖ.ϖ)

end Stab


namespace IsometricAut

end IsometricAut

end Actions

section Hom

variable [DecidableEq K]

end Hom

section Glue

variable [DecidableEq K] {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

end Glue

end CerednikDrinfeld.Omega

end
