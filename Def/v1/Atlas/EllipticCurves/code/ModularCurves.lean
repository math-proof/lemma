/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Manifold

open scoped ContDiff

/-- Definition 18.4 (Complex structure): a `ComplexStructure` on a topological space
`X` is a `ChartedSpace ℂ X` together with the property that `X` is a real-analytic
manifold modelled on `ℂ` (i.e., the transition maps between charts are holomorphic). -/


namespace Def1811

/-- The reduction-mod-`N` group homomorphism `SL₂(ℤ) → SL₂(ℤ/Nℤ)`. -/
noncomputable def SL2_reductionMod (N : ℕ) : SL(2, ℤ) →* SL(2, ZMod N) :=
  SpecialLinearGroup.map (Int.castRingHom (ZMod N))

/-- Definition 18.11: the principal congruence subgroup `Γ(N) ⊆ SL₂(ℤ)`, consisting of
matrices congruent to the identity modulo `N`. -/
def PrincipalCongruenceSubgroup (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma N

/-- The Hecke-type congruence subgroup `Γ₀(N) ⊆ SL₂(ℤ)` of matrices that are upper
triangular modulo `N`. -/
def CongruenceSubgroup0 (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma0 N

/-- The Hecke-type congruence subgroup `Γ₁(N) ⊆ SL₂(ℤ)` of matrices that are
upper-unitriangular modulo `N`. -/
def CongruenceSubgroup1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma1 N

/-- Definition 18.11: a subgroup `H ⊆ SL₂(ℤ)` is a *congruence subgroup* if it
contains some principal congruence subgroup `Γ(N)`. -/
def IsCongruenceSubgroup (H : Subgroup SL(2, ℤ)) : Prop :=
  CongruenceSubgroup.IsCongruenceSubgroup H

/-- The open modular curve `Y_Γ := Γ \ ℍ`, the quotient of the upper half-plane by a
congruence subgroup `Γ`. -/
noncomputable def ModularCurveOpen (Γ : Subgroup SL(2, ℤ)) : Type :=
  Quotient (MulAction.orbitRel Γ UpperHalfPlane)

/-- The extended upper half-plane `ℍ* = ℍ ∪ ℚ ∪ {∞}` (cusps adjoined), modelled here
as an `opaque` type pending a formal definition. -/
opaque ExtendedUpperHalfPlane : Type

/-- Axiom: there is a natural `SL₂(ℤ)`-action on `ℍ*`. -/
noncomputable def ModularCurve (Γ : Subgroup SL(2, ℤ)) : Type :=
  Quotient (MulAction.orbitRel Γ ExtendedUpperHalfPlane)

end Def1811
