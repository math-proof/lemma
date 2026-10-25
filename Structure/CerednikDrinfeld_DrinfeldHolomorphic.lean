import Instance.CerednikDrinfeld_DrinfeldUpperHalfPlane
import Instance.CerednikDrinfeld_MumfordQuotient
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Algebra.Polynomial.Eval.Defs
import Instance.CerednikDrinfeld_DrinfeldHolomorphic

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open Filter CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace CerednikDrinfeld.Omega

variable (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

structure PseudoUniformizer where

  ϖ : K₀
  pos : 0 < Valued.v (algebraMap K₀ K ϖ)
  lt_one : Valued.v (algebraMap K₀ K ϖ) < 1
  scale : ∀ a : K₀, a ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K ϖ) ^ N ≤ Valued.v (algebraMap K₀ K a) ∧
    Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ))⁻¹ ^ N

variable {K₀ K} (ϖ : PseudoUniformizer K₀ K)


structure RatPair (K : Type) [Field K] where

  num : Polynomial K

  den : Polynomial K

namespace RatPair


end RatPair

section Hol

variable (K)


variable {K}


variable (K) in


end Hol


section Actions

variable [DecidableEq K]


section Stab


omit [DecidableEq K] in


end Stab


variable (K₀ K) in

structure IsometricAut where

  toRingEquiv : K ≃+* K
  isometry : ∀ x : K, Valued.v (toRingEquiv x) = Valued.v x
  fix : ∀ a : K₀, toRingEquiv (algebraMap K₀ K a) = algebraMap K₀ K a

namespace IsometricAut

omit [DecidableEq K] in


end IsometricAut

end Actions


section Hom

variable [DecidableEq K]


end Hom

section Glue

variable [DecidableEq K] {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

set_option linter.unusedVariables false in


end Glue


end CerednikDrinfeld.Omega

end
