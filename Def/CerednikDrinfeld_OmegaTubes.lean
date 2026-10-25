import Instance.CerednikDrinfeld_DrinfeldHolomorphic

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace CerednikDrinfeld.Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

def stdEdgeTube : Set K :=
  {z | z ∈ upperHalfPlane K₀ K ∧ Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v z ∧ Valued.v z < 1}

omit [DecidableEq K] in

omit [DecidableEq K] in

def vertexTube (g : PGL(2, K₀)) : Set K :=
  {z | z ∈ upperHalfPlane K₀ K ∧ pmoebius K₀ g⁻¹ z ∈ affinoid ϖ 0}

def edgeTube (g : PGL(2, K₀)) : Set K :=
  {z | z ∈ upperHalfPlane K₀ K ∧ pmoebius K₀ g⁻¹ z ∈ stdEdgeTube ϖ}

end CerednikDrinfeld.Omega

end
