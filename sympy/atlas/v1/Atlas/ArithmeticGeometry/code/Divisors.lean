/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.DegreePullback
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.DegreePullback
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion

structure ClosedPointRes (k : Type*) [Field k] where
  residueField : Type*
  [residueFieldField : Field residueField]
  [residueFieldAlgebra : Algebra k residueField]
  [finiteDimensional : FiniteDimensional k residueField]

attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional

namespace ClosedPointRes

variable {k : Type*} [Field k]

noncomputable def degreePoint (P : ClosedPointRes k) : ℕ :=
  Module.finrank k P.residueField


end ClosedPointRes

abbrev CurveDivisor (C : Type*) := C →₀ ℤ

namespace CurveDivisor

variable {C : Type*}

noncomputable def coeff (D : CurveDivisor C) (P : C) : ℤ := D P

noncomputable def divisorSupport (D : CurveDivisor C) : Finset C := D.support

variable (C) in
noncomputable def degree : CurveDivisor C →+ ℤ :=
  Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

noncomputable def degreeWeighted (deg : C → ℕ) : CurveDivisor C →+ ℤ :=
  Finsupp.liftAddHom (fun p => (deg p : ℤ) • AddMonoidHom.id ℤ)

noncomputable instance galoisSMul : SMul G (CurveDivisor C) :=
  Finsupp.comapSMul

noncomputable instance galoisMulAction : MulAction G (CurveDivisor C) :=
  Finsupp.comapMulAction


def IsDefinedOverK (G : Type*) [Group G] [MulAction G C]
    (D : CurveDivisor C) : Prop :=
  ∀ (σ : G), σ • D = D


end GaloisAction

noncomputable def divZeros (D : CurveDivisor C) : CurveDivisor C := D ⊔ 0

noncomputable def divPoles (D : CurveDivisor C) : CurveDivisor C := (-D) ⊔ 0

abbrev ClosedPoint (G : Type*) (C : Type*) [Group G] [MulAction G C] :=
  MulAction.orbitRel.Quotient G C

namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

def mk (P : C) : ClosedPoint G C := ⟦P⟧

def toOrbit (P : ClosedPoint G C) : Set C :=
  MulAction.orbitRel.Quotient.orbit P

noncomputable def degreeClosedPoint (k K : Type*) [Field k] [Field K] [Algebra k K] : ℕ :=
  Module.finrank k K


abbrev RationalDivisor (G : Type*) (C : Type*) [Group G] [MulAction G C] :=
  ClosedPoint G C →₀ ℤ

namespace RationalDivisor

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

noncomputable def coeff (D : RationalDivisor G C) (P : ClosedPoint G C) : ℤ := D P

noncomputable def rationalDivisorSupport (D : RationalDivisor G C) :
    Finset (ClosedPoint G C) := D.support

end RationalDivisor

class CurveWithOrd (C : Type*) (F : Type*) [Field F] where
  ord : C → Fˣ → ℤ
  ord_mul : ∀ (P : C) (f g : Fˣ), ord P (f * g) = ord P f + ord P g
  ord_add : ∀ (P : C) (f g : Fˣ) (hfg : (f : F) + (g : F) ≠ 0),
    ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥ min (ord P f) (ord P g)
  uniformizer_exists : ∀ (P : C), ∃ (π : Fˣ), ord P π = 1


class FunctionFieldCurve (C : Type*) (F : Type*) [Field F]
    extends CurveWithOrd C F where
  isCoordRingElem : Fˣ → Prop
  fraction_rep : ∀ (f : Fˣ), ∃ (g h : Fˣ), isCoordRingElem g ∧ isCoordRingElem h ∧
    f = g * h⁻¹
  ord_nonneg_of_coordRingElem : ∀ (f : Fˣ), isCoordRingElem f →
    ∀ (P : C), 0 ≤ CurveWithOrd.ord (F := F) P f
  zeroLocus_finite : ∀ (f : Fˣ), isCoordRingElem f →
    Set.Finite {P : C | 0 < CurveWithOrd.ord (F := F) P f}


theorem FunctionFieldCurve.coordRing_finite_support {C : Type*} {F : Type*} [Field F]
    [inst : FunctionFieldCurve C F] (f : Fˣ) (hf : inst.isCoordRingElem f) :
    (Function.support (fun P => CurveWithOrd.ord (C := C) (F := F) P f)).Finite := by
  apply Set.Finite.subset (inst.zeroLocus_finite f hf)
  intro P hP
  simp only [Set.mem_setOf_eq, Function.mem_support] at hP ⊢
  have := inst.ord_nonneg_of_coordRingElem f hf P
  omega

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [CurveWithOrd C F]

theorem ord_one (P : C) : ord (F := F) P 1 = 0 := by
  have h := ord_mul (F := F) P 1 1
  simp at h
  linarith

theorem ord_inv (P : C) (f : Fˣ) : ord (F := F) P f⁻¹ = -ord P f := by
  have h := ord_mul (F := F) P f f⁻¹
  simp only [mul_inv_cancel] at h
  rw [ord_one] at h
  linarith

end CurveWithOrd

theorem ord_finite_support {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]
    (f : Fˣ) :
    (Function.support (fun P => CurveWithOrd.ord (C := C) (F := F) P f)).Finite := by

  obtain ⟨g, h, hg, hh, hf⟩ := FunctionFieldCurve.fraction_rep (C := C) (F := F) f

  have hg_fin := FunctionFieldCurve.coordRing_finite_support g hg
  have hh_fin := FunctionFieldCurve.coordRing_finite_support h hh

  apply Set.Finite.subset (hg_fin.union hh_fin)
  intro P hP
  simp only [Function.mem_support, Set.mem_union] at hP ⊢


  by_contra h_contra
  push Not at h_contra
  obtain ⟨hgP, hhP⟩ := h_contra
  apply hP
  rw [hf, CurveWithOrd.ord_mul, CurveWithOrd.ord_inv]
  omega

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

noncomputable def principalDivisor (f : Fˣ) : CurveDivisor C :=
  Finsupp.ofSupportFinite (fun P => ord P f) (ord_finite_support f)

@[simp]
theorem principalDivisor_apply (f : Fˣ) (P : C) :
    (principalDivisor f : CurveDivisor C) P = ord P f := by
  simp [principalDivisor, Finsupp.ofSupportFinite]

@[simp]
theorem principalDivisor_one : principalDivisor (C := C) (F := F) (1 : Fˣ) = 0 := by
  ext P
  simp [ord_one]

theorem principalDivisor_mul (f g : Fˣ) :
    principalDivisor (C := C) (f * g) = principalDivisor f + principalDivisor g := by
  ext P
  simp [ord_mul]

theorem principalDivisor_inv (f : Fˣ) :
    principalDivisor (C := C) f⁻¹ = -principalDivisor f := by
  ext P
  simp [ord_inv]

noncomputable def principalDivisorHom :
    Fˣ →* Multiplicative (CurveDivisor C) where
  toFun f := Multiplicative.ofAdd (principalDivisor f)
  map_one' := by simp
  map_mul' f g := by
    simp only [principalDivisor_mul]
    rfl

noncomputable def principalDivisors : AddSubgroup (CurveDivisor C) where
  carrier := Set.range (fun f : Fˣ => principalDivisor (C := C) f)
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f * g, principalDivisor_mul f g⟩
  zero_mem' := ⟨1, principalDivisor_one⟩
  neg_mem' := by
    rintro _ ⟨f, rfl⟩
    exact ⟨f⁻¹, principalDivisor_inv f⟩

def IsPrincipal (D : CurveDivisor C) : Prop :=
  D ∈ principalDivisors (F := F)

noncomputable def divAddHom : Additive Fˣ →+ CurveDivisor C where
  toFun f := principalDivisor (Additive.toMul f)
  map_zero' := by show principalDivisor (1 : Fˣ) = 0; exact principalDivisor_one
  map_add' f g := by
    show principalDivisor (_ * _) = principalDivisor _ + principalDivisor _
    exact principalDivisor_mul _ _


abbrev PicardGroup (C : Type*) (F : Type*) [Field F] [FunctionFieldCurve C F] :=
  CurveDivisor C ⧸ principalDivisors (C := C) (F := F)

noncomputable def toPicardGroup : CurveDivisor C →+ PicardGroup C F :=
  QuotientAddGroup.mk' (principalDivisors (F := F))

class CurveWithConstants (C : Type*) (k : Type*) (F : Type*) [Field k] [Field F]
    [Algebra k F] extends FunctionFieldCurve C F where
  const_isCoordRingElem : ∀ (a : kˣ),
    toFunctionFieldCurve.isCoordRingElem (Units.map (algebraMap k F).toMonoidHom a)
  const_inv_isCoordRingElem : ∀ (a : kˣ),
    toFunctionFieldCurve.isCoordRingElem (Units.map (algebraMap k F).toMonoidHom a)⁻¹
  algClosed_in_extension : ∀ (x : F), IsAlgebraic k x → x ∈ (algebraMap k F).range
  ord_zero_algebraic : ∀ (f : Fˣ), (∀ P : C, CurveWithOrd.ord P f = 0) →
    IsAlgebraic k (f : F)
  residue_eval : ∀ (P : C), ∃ (evalP : F →ₗ[k] k),
    ∀ (f : Fˣ), CurveWithOrd.ord P f ≥ 0 → evalP (f : F) = 0 →
      CurveWithOrd.ord P f ≥ 1


theorem CurveWithConstants.ord_constant {C : Type*} {k : Type*} {F : Type*}
    [Field k] [Field F] [Algebra k F] [inst : CurveWithConstants C k F]
    (P : C) (a : kˣ) :
    CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a) = 0 := by
  have h_pos : (0 : ℤ) ≤ CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a) :=
    inst.toFunctionFieldCurve.ord_nonneg_of_coordRingElem _ (inst.const_isCoordRingElem a) P
  have h_neg : (0 : ℤ) ≤ CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a)⁻¹ :=
    inst.toFunctionFieldCurve.ord_nonneg_of_coordRingElem _ (inst.const_inv_isCoordRingElem a) P
  have h_inv : CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a)⁻¹ =
    -CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a) :=
    CurveWithOrd.ord_inv P _
  omega

noncomputable def constantsEmb : kˣ →* Fˣ :=
  Units.map (algebraMap k F).toMonoidHom

structure FunctionFieldPlace (F : Type*) [Field F] (k : Type*) [Field k] where
  valuationSubring : ValuationSubring F
  isPrincipalIdealRing : IsPrincipalIdealRing valuationSubring
  notIsField : ¬ IsField valuationSubring
  residueFieldEquiv : letI := valuationSubring.isLocalRing
    IsLocalRing.ResidueField valuationSubring ≃+* k

namespace FunctionFieldPlace

variable {F : Type*} [Field F] {k : Type*} [Field k]

instance (P : FunctionFieldPlace F k) : IsPrincipalIdealRing P.valuationSubring :=
  P.isPrincipalIdealRing

instance (P : FunctionFieldPlace F k) : IsFractionRing P.valuationSubring F :=
  inferInstance

end FunctionFieldPlace

abbrev FunctionFieldDivisor (F : Type*) [Field F] (k : Type*) [Field k] :=
  FunctionFieldPlace F k →₀ ℤ

namespace FunctionFieldDivisor

variable {F : Type*} [Field F] {k : Type*} [Field k]

noncomputable def coeff (D : FunctionFieldDivisor F k) (P : FunctionFieldPlace F k) : ℤ :=
  D P

noncomputable def divisorSupport (D : FunctionFieldDivisor F k) :
    Finset (FunctionFieldPlace F k) :=
  D.support

end FunctionFieldDivisor

noncomputable section

namespace ArithmeticGeometry

namespace FunctionField_k

variable {k : Type*} [Field k]
variable {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]

def Morphism.ramificationIndex
    (φ : F₂ →+* F₁)
    (ordP : F₁ˣ → ℤ)
    (tQ : F₂ˣ)
    : ℤ :=
  ordP (Units.map φ.toMonoidHom tQ)


def Morphism.IsUnramifiedAt
    (φ : F₂ →+* F₁)
    (ordP : F₁ˣ → ℤ)
    (tQ : F₂ˣ) : Prop :=
  Morphism.ramificationIndex φ ordP tQ = 1


def Morphism.IsUnramified
    (φ : F₂ →+* F₁)
    (places : Type*)
    (ordAt : places → F₁ˣ → ℤ)
    (uniformizerAt : places → F₂ˣ)
    : Prop :=
  ∀ P : places, Morphism.IsUnramifiedAt φ (ordAt P) (uniformizerAt P)


end FunctionField_k

end ArithmeticGeometry

namespace CurveWithConstants

variable {C : Type*} {k : Type*} {F : Type*} [Field k] [Field F]
  [Algebra k F] [CurveWithConstants C k F]

open CurveWithOrd CurveDivisor

structure CurveMorphismData (C₁ : Type*) (C₂ : Type*) where
  toFun : C₁ → C₂
  ramificationIndex : C₁ → ℤ
  fiber : C₂ → Finset C₁
  fiber_maps_to : ∀ Q : C₂, ∀ P ∈ fiber Q, toFun P = Q
  fiber_complete : ∀ Q : C₂, ∀ P : C₁, toFun P = Q → P ∈ fiber Q
  residueFieldDegreeRatio : C₁ → ℤ

noncomputable section

namespace CurveMorphismData

variable {C₁ C₂ : Type*}


def pullbackPoint (φ : CurveMorphismData C₁ C₂) (Q : C₂) : CurveDivisor C₁ :=
  (φ.fiber Q).sum (fun P => Finsupp.single P (φ.ramificationIndex P))

def pullback (φ : CurveMorphismData C₁ C₂) : CurveDivisor C₂ →+ CurveDivisor C₁ :=
  Finsupp.liftAddHom (fun Q => {
    toFun := fun n => n • φ.pullbackPoint Q
    map_zero' := by simp
    map_add' := by intros; simp [add_smul]
  })


def pushforward (φ : CurveMorphismData C₁ C₂) : CurveDivisor C₁ →+ CurveDivisor C₂ :=
  Finsupp.liftAddHom (fun P => {
    toFun := fun n => Finsupp.single (φ.toFun P) n
    map_zero' := by simp
    map_add' := by intros; simp [Finsupp.single_add]
  })

def pushforwardGeneral (φ : CurveMorphismData C₁ C₂) : CurveDivisor C₁ →+ CurveDivisor C₂ :=
  Finsupp.liftAddHom (fun P => {
    toFun := fun n => Finsupp.single (φ.toFun P) (n * φ.residueFieldDegreeRatio P)
    map_zero' := by simp
    map_add' := by intros; simp [Finsupp.single_add, add_mul]
  })


end CurveMorphismData

end

namespace ArithmeticGeometry

variable {k : Type*} [Field k]
