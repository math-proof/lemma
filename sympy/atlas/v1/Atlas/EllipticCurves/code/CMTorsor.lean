/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ClassGroup
import sympy.atlas.v1.Atlas.EllipticCurves.code.ComplexMultiplication
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic

namespace FieldNormTrace

section General

/-- The field norm `K → k` of a `k`-algebra `K`, packaged as a monoid homomorphism. -/
noncomputable abbrev fieldNorm (k : Type*) {K : Type*}
    [CommRing k] [Ring K] [Algebra k K] : K →* k :=
  Algebra.norm k

/-- The field trace `K → k` of a `k`-algebra `K`, packaged as a `k`-linear map. -/
noncomputable abbrev fieldTrace (k : Type*) (K : Type*)
    [CommRing k] [CommRing K] [Algebra k K] : K →ₗ[k] k :=
  Algebra.trace k K

end General

section Quadratic

variable {D : ℤ}

/-- The discriminant `t² - 4n` of a monic quadratic `x² - t x + n`. -/
def disc (t n : ℤ) : ℤ := t ^ 2 - 4 * n

/-- The integer trace of `τ ∈ ℤ√d`, defined as `2 · τ.re`. -/
def traceZ : ℤ := 2 * τ.re

/-- The discriminant of `τ ∈ ℤ√d`, given by `disc (traceZ τ) (N τ)`. -/
def discZsqrtd : ℤ := disc (traceZ τ) (Zsqrtd.norm τ)

/-- `D` is an imaginary quadratic discriminant if `D < 0` and `D ≡ 0` or `1 (mod 4)`. -/
def IsImaginaryQuadraticDiscriminant (D : ℤ) : Prop :=
  D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

/-- `D` is a fundamental imaginary quadratic discriminant if it is an imaginary quadratic
discriminant and is not of the form `u² · D'` for `u > 1` and another imaginary quadratic
discriminant `D'`. -/
def IsFundamentalImaginaryQuadraticDiscriminant (D : ℤ) : Prop :=
  IsImaginaryQuadraticDiscriminant D ∧
    ∀ u D' : ℤ, u > 1 → IsImaginaryQuadraticDiscriminant D' → D ≠ u ^ 2 * D'

/-- A decomposition `D = u² · D_K` of an imaginary quadratic discriminant `D` into the
conductor `u ≥ 1` and the fundamental discriminant `D_K` of the maximal order. -/
structure ImaginaryQuadraticDiscriminantDecomposition (D : ℤ) where
  u : ℤ
  D_K : ℤ
  hu : u ≥ 1
  hD_K : IsFundamentalImaginaryQuadraticDiscriminant D_K
  hD : D = u ^ 2 * D_K

/-- Convenient abbreviation `FractionalOIdeal R K` for the type of fractional `R`-ideals
in the fraction field `K`. -/
abbrev FractionalOIdeal (R : Type*) [CommRing R] [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  FractionalIdeal R⁰ K

namespace FractionalOIdeal

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

open FractionalIdeal

set_option linter.unusedSectionVars false in

/-- The ideal norm `N(𝔞) := |𝒪/𝔞|`, defined as the cardinality of the quotient ring. -/
noncomputable def idealNorm (𝔞 : Ideal 𝒪) : ℕ := Submodule.cardQuot 𝔞

/-- The norm of a fractional ideal `𝔟 = (1/d) · 𝔟.num`: `N(𝔟) = N(𝔟.num) / |N(𝔟.den)|`,
as a rational number. -/
noncomputable def fractionalIdealNorm (𝔟 : FractionalIdeal 𝒪⁰ K) : ℚ :=
  (Ideal.absNorm 𝔟.num : ℚ) / |Algebra.norm ℤ (𝔟.den : 𝒪)|

/-- An imaginary quadratic order, presented by a trace `t` and a norm `n` such that the
discriminant `t² - 4n` is negative and `≡ 0` or `1 (mod 4)`. -/
structure ImaginaryQuadraticOrder where
  t : ℤ
  n : ℤ
  hdisc_neg : t ^ 2 - 4 * n < 0
  hdisc_mod : (t ^ 2 - 4 * n) % 4 = 0 ∨ (t ^ 2 - 4 * n) % 4 = 1

/-- The discriminant `t² - 4n` of an imaginary quadratic order. -/
def ImaginaryQuadraticOrder.discriminant (𝒪 : ImaginaryQuadraticOrder) : ℤ :=
  𝒪.t ^ 2 - 4 * 𝒪.n

/-- Two imaginary quadratic orders agree (define the same order) when they have the same
discriminant and the same trace parity. -/
def ImaginaryQuadraticOrder.SameOrder (𝒪₁ 𝒪₂ : ImaginaryQuadraticOrder) : Prop :=
  𝒪₁.discriminant = 𝒪₂.discriminant ∧ 𝒪₁.t % 2 = 𝒪₂.t % 2

/-- Construct an `ImaginaryQuadraticOrder` of discriminant `D = u² · D_K` from the
decomposition `dec` into a conductor `u` and a fundamental discriminant `D_K`. -/
def orderFromDecomposition {D : ℤ}
    (dec : ImaginaryQuadraticDiscriminantDecomposition D) :
    ImaginaryQuadraticOrder where


  t := if dec.D_K % 4 = 0 then 0 else dec.u


  n := if dec.D_K % 4 = 0 then
    -(dec.u ^ 2 * (dec.D_K / 4))
  else
    -(dec.u ^ 2 * ((dec.D_K - 1) / 4))
  hdisc_neg := by
    have hu_sq_pos : dec.u ^ 2 ≥ 1 := by nlinarith [dec.hu]
    rcases dec.hD_K.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
      have hk_neg : k < 0 := by nlinarith [dec.hD_K.1.1]
      have : dec.D_K / 4 = k := by omega
      rw [this]; nlinarith
    · have h0f : ¬(dec.D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (dec.D_K - 1) % 4 = 0 by omega)
      have hm_neg : m < 0 := by nlinarith [dec.hD_K.1.1]
      have : (dec.D_K - 1) / 4 = m := by omega
      rw [this]; nlinarith
  hdisc_mod := by
    rcases dec.hD_K.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]; left; omega
    · have h0f : ¬(dec.D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (dec.D_K - 1) % 4 = 0 by omega)
      have hm_eq : (dec.D_K - 1) / 4 = m := by omega
      rw [hm_eq]
      rcases (show dec.u % 2 = 0 ∨ dec.u % 2 = 1 by omega) with hu | hu
      · left
        obtain ⟨j, hj⟩ := Int.dvd_of_emod_eq_zero hu
        have : dec.u ^ 2 - 4 * -(dec.u ^ 2 * m) = dec.u ^ 2 * (4 * m + 1) := by ring
        rw [this, hj]; ring_nf; omega
      · right
        obtain ⟨j, hj⟩ := Int.dvd_of_emod_eq_zero (show (dec.u - 1) % 2 = 0 by omega)
        have hu_eq : dec.u = 2 * j + 1 := by omega
        have : dec.u ^ 2 - 4 * -(dec.u ^ 2 * m) = dec.u ^ 2 * (4 * m + 1) := by ring
        rw [this, hu_eq]; ring_nf; omega

/-- The maximal order of an imaginary quadratic field with fundamental discriminant `D_K`,
constructed as an `ImaginaryQuadraticOrder`. -/
def maximalOrder (D_K : ℤ) (hfund : IsFundamentalImaginaryQuadraticDiscriminant D_K) :
    ImaginaryQuadraticOrder where
  t := if D_K % 4 = 0 then 0 else 1
  n := if D_K % 4 = 0 then -(D_K / 4) else -((D_K - 1) / 4)
  hdisc_neg := by
    rcases hfund.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
      have : D_K / 4 = k := by omega
      rw [this]; nlinarith [hfund.1.1]
    · have h0f : ¬(D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (D_K - 1) % 4 = 0 by omega)
      have : (D_K - 1) / 4 = m := by omega
      rw [this]; nlinarith [hfund.1.1]
  hdisc_mod := by
    rcases hfund.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]; left; omega
    · have h0f : ¬(D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]; right
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (D_K - 1) % 4 = 0 by omega)
      have : (D_K - 1) / 4 = m := by omega
      rw [this]; omega

/-- `𝒪` is a suborder of `𝒪_K` with index `u` if its discriminant is `u²` times that of
`𝒪_K` and the traces satisfy `𝒪.t = 2a + u · 𝒪_K.t` for some integer `a`. -/
def ImaginaryQuadraticOrder.IsSuborderOfIndex (𝒪 𝒪_K : ImaginaryQuadraticOrder) (u : ℤ) : Prop :=
  u ≥ 1 ∧ 𝒪.discriminant = u ^ 2 * 𝒪_K.discriminant ∧
  ∃ a : ℤ, 𝒪.t = 2 * a + u * 𝒪_K.t

/-- The order (multiplier ring) of a fractional ideal `I` in `K`: the set of `x : K` such
that `x · I ⊆ I`. -/
def idealOrder (I : FractionalIdeal R⁰ K) : Set K :=
  {x : K | ∀ y ∈ (I : Submodule R K), x * y ∈ (I : Submodule R K)}

/-- A fractional ideal `I` is *proper* if its order equals the image of `R` in `K`, i.e.
its multiplier ring is exactly `R` itself. -/
def IsProper (I : FractionalIdeal R⁰ K) : Prop :=
  idealOrder I = Set.range (algebraMap R K)

/-- The canonical `ℤ`-linear equivalence `ℤ√d ≃ₗ[ℤ] (Fin 2 → ℤ)` sending `α` to
`![α.re, α.im]`. Exhibits `ℤ√d` as a free `ℤ`-module of rank 2. -/
noncomputable def zsqrtdLinearEquivFin2 (d : ℤ) : (ℤ√d) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x.re, x.im]
  invFun v := ⟨v 0, v 1⟩
  map_add' x y := by ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  map_smul' r x := by ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  left_inv x := by ext <;> simp
  right_inv v := by ext i; fin_cases i <;> simp

/-- `ℤ√d` is free as a `ℤ`-module, via the equivalence with `Fin 2 → ℤ`. -/
noncomputable instance instModuleFreeZsqrtd : Module.Free ℤ (ℤ√d) :=
  Module.Free.of_equiv (zsqrtdLinearEquivFin2 d).symm

/-- `ℤ√d` is finitely generated as a `ℤ`-module (in fact rank 2). -/
noncomputable instance instModuleFiniteZsqrtd : Module.Finite ℤ (ℤ√d) :=
  Module.Finite.equiv (zsqrtdLinearEquivFin2 d).symm

/-- The conjugate of an ideal `I ⊆ ℤ√d`: the image of `I` under the conjugation ring
homomorphism `star`. -/
def conjIdeal (I : Ideal (ℤ√d)) : Ideal (ℤ√d) :=
  Ideal.map (starRingEnd (ℤ√d)) I

/-- The ideal norm in `ℤ√d`, given by the cardinality of the quotient `(ℤ√d) / I`. -/
noncomputable def idealNormZsqrtd (I : Ideal (ℤ√d)) : ℕ :=
  Nat.card ((ℤ√d) ⧸ I)

/-- Characterisation of properness for nonzero fractional ideals of `ℤ√d` (imaginary
quadratic case): `I` is proper iff `I` is invertible. -/
noncomputable def fractionalIdealNormZsqrtd (hd : d < 0) [IsDomain (ℤ√d)]
    (K : Type*) [Field K] [Algebra (ℤ√d) K] [IsFractionRing (ℤ√d) K]
    (𝔞 : FractionalIdeal (ℤ√d)⁰ K) : ℚ :=
  (idealNormZsqrtd 𝔞.num : ℚ) / |(Zsqrtd.norm (𝔞.den : ℤ√d) : ℚ)|

/-- Multiplicativity of the fractional ideal norm in `ℤ√d` on proper ideals:
`N(𝔞 · 𝔟) = N(𝔞) · N(𝔟)`. -/
end Quadratic

end ProperIdealInvertible

namespace IdealClassGroup

open nonZeroDivisors FractionalIdeal

section General

variable (R : Type*) [CommRing R] [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K]

/-- The group of invertible fractional ideals of `R` in its field of fractions `K`. -/
abbrev InvertibleFractionalIdeals := (FractionalIdeal R⁰ K)ˣ

/-- The subgroup of principal invertible fractional ideals (image of `K*` under
`toPrincipalIdeal`). -/
abbrev PrincipalFractionalIdeals := (toPrincipalIdeal R K).range

/-- The subgroup of principal fractional ideals is normal in the group of invertible
fractional ideals (the ambient group is abelian). -/
instance : (PrincipalFractionalIdeals R K).Normal :=
  PrincipalIdeals.normal

/-- Identification of the quotient
`InvertibleFractionalIdeals / PrincipalFractionalIdeals` with the ideal class group
`Cl(R)` (via Mathlib's `ClassGroup.equiv`). -/
noncomputable def classGroup_mulEquiv :
    InvertibleFractionalIdeals R K ⧸ PrincipalFractionalIdeals R K ≃* ClassGroup R :=
  (ClassGroup.equiv K).symm

/-- The quotient of invertible fractional ideals by principal ones inherits an abelian
group structure. -/
noncomputable instance instCommGroupQuotient :
    CommGroup (InvertibleFractionalIdeals R K ⧸ PrincipalFractionalIdeals R K) :=
  QuotientGroup.Quotient.commGroup _

/-- The class group `Cl(R)` is an abelian group. -/
noncomputable instance : CommGroup (ClassGroup R) := inferInstance

end General

section ImaginaryQuadratic

open ProperIdealInvertible

variable {d : ℤ}

/-- Identification of the quotient
`InvertibleFractionalIdeals(ℤ√d) / PrincipalFractionalIdeals(ℤ√d)` with the class group
`Cl(ℤ√d)` (in the imaginary quadratic case). -/
noncomputable def classGroupQuotient_imaginaryQuadratic
    [IsDomain (ℤ√d)]
    (K : Type*) [Field K] [Algebra (ℤ√d) K] [IsFractionRing (ℤ√d) K] :
    (FractionalIdeal (ℤ√d)⁰ K)ˣ ⧸ (toPrincipalIdeal (ℤ√d) K).range ≃*
    ClassGroup (ℤ√d) :=
  classGroup_mulEquiv (ℤ√d) K

end ImaginaryQuadratic

section ClassGroupQuotientEquiv

open ComplexLattice

variable (𝒪 : Subring ℂ) [IsDomain 𝒪]

/-- Specialised version for `𝒪 = ℤ√d`: the quotient
`(FractionalIdeal (ℤ√d) K)ˣ / Principal` is `Cl(ℤ√d)`. -/
noncomputable def classGroupQuotient_Zsqrtd (d : ℤ) [IsDomain (ℤ√d)]
    (K : Type*) [Field K] [Algebra (ℤ√d) K] [IsFractionRing (ℤ√d) K] :
    (FractionalIdeal (ℤ√d)⁰ K)ˣ ⧸ (toPrincipalIdeal (ℤ√d) K).range ≃*
    ClassGroup (ℤ√d) :=
  classGroup_mulEquiv (ℤ√d) K

end ClassGroupQuotientEquiv

end IdealClassGroup

namespace IdealTorsion

variable {𝒪 : Type*} [CommRing 𝒪]
variable {E : Type*} [AddCommGroup E] [Module 𝒪 E]

/-- The `𝔞`-torsion submodule of an `𝒪`-module `E`: the set of `P ∈ E` such that
`α · P = 0` for every `α ∈ 𝔞`. -/
def idealTorsion (𝔞 : Ideal 𝒪) : Submodule 𝒪 E where
  carrier := {P : E | ∀ α ∈ 𝔞, α • P = 0}
  zero_mem' := fun α _ => smul_zero α
  add_mem' := fun {P Q} hP hQ α hα => by rw [smul_add, hP α hα, hQ α hα, add_zero]
  smul_mem' := fun r {P} hP α hα => by
    rw [smul_comm]
    exact smul_eq_zero_of_right r (hP α hα)

/-- The `𝔞`-torsion submodule viewed as an additive subgroup of `E`. -/
def idealTorsionAddSubgroup (𝔞 : Ideal 𝒪) : AddSubgroup E :=
  (idealTorsion 𝔞).toAddSubgroup

end IdealTorsion

namespace CMTorsorAction

open IdealTorsion NormTrace

variable {𝒪 : Type*} [CommRing 𝒪]

/-- A *CM-module* over `𝒪` is an `𝒪`-module `E` together with the data of an ideal
`latticeIdeal ⊆ 𝒪` and an `𝒪`-linear equivalence `E ≃ₗ[𝒪] 𝒪 / latticeIdeal`. -/
class IsCMModule (𝒪 : Type*) [CommRing 𝒪] (E : Type*) [AddCommGroup E] [Module 𝒪 E] where
  latticeIdeal : Ideal 𝒪
  linearEquiv : E ≃ₗ[𝒪] 𝒪 ⧸ (latticeIdeal : Submodule 𝒪 𝒪)

/-- Data describing a CM-isogeny `𝒪/𝔟 → 𝒪/targetIdeal` corresponding to multiplication by
an ideal `𝔞`: includes the target ideal (the colon ideal `(𝔟 : 𝔞)`) and the relation
`𝔞 · targetIdeal = 𝔟`. -/
structure CMIsogenyData (𝒪 : Type*) [CommRing 𝒪] (𝔟 : Ideal 𝒪) (𝔞 : Ideal 𝒪) where
  targetIdeal : Ideal 𝒪
  le_target : 𝔟 ≤ targetIdeal
  ideal_mul_target_le : 𝔞 * targetIdeal ≤ 𝔟
  target_eq_colon :
    (targetIdeal : Submodule 𝒪 𝒪) = (𝔟 : Submodule 𝒪 𝒪).colon (𝔞 : Set 𝒪)
  ideal_mul_target_eq : 𝔞 * targetIdeal = 𝔟

/-- The `𝒪`-linear map `𝒪/𝔟 → 𝒪/targetIdeal` underlying a `CMIsogenyData`. -/
noncomputable def CMIsogenyData.toLinearMap {𝔟 𝔞 : Ideal 𝒪} (φ : CMIsogenyData 𝒪 𝔟 𝔞) :
    (𝒪 ⧸ (𝔟 : Submodule 𝒪 𝒪)) →ₗ[𝒪] (𝒪 ⧸ (φ.targetIdeal : Submodule 𝒪 𝒪)) :=
  (𝔟 : Submodule 𝒪 𝒪).mapQ φ.targetIdeal LinearMap.id
    (by rw [Submodule.comap_id]; exact φ.le_target)

/-- The degree of the CM-isogeny `φ`, defined as the cardinality of its kernel. -/
noncomputable def degIsogeny {𝔟 𝔞 : Ideal 𝒪} (φ : CMIsogenyData 𝒪 𝔟 𝔞) : ℕ :=
  Nat.card (LinearMap.ker φ.toLinearMap)
