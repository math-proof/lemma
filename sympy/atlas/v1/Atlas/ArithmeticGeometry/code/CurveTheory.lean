/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.MorphismsCurves
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.RegularLocalRings
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RegularLocalRings

noncomputable section

open Module IsDiscreteValuationRing

namespace ArithmeticGeometry

section DVRNormalization

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

structure RationalMapToProj (K : Type*) [Field K] (n : ℕ) where
  coords : Fin (n + 1) → K
  coords_ne_zero : ∃ i, coords i ≠ 0

def RationalMapToProj.IsRegularAt {K : Type*} [Field K] {n : ℕ}
    (φ : RationalMapToProj K n)
    (R : Type*) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K] : Prop :=
  ∃ j, φ.coords j ≠ 0 ∧
    (∀ i, IsLocalization.IsInteger R (φ.coords i * (φ.coords j)⁻¹))

def RationalMapToProj.ExtendsMorphism {K : Type*} [Field K] {n : ℕ}
    (φ : RationalMapToProj K n)
    {P : Type*} (R : P → Type*)
    [∀ p, CommRing (R p)] [∀ p, IsDomain (R p)]
    [∀ p, Algebra (R p) K] [∀ p, IsFractionRing (R p) K] : Prop :=
  ∀ p, φ.IsRegularAt (R p)

structure MorphismToProj (K : Type*) [Field K] (n : ℕ)
    {P : Type*} (R : P → Type*)
    [∀ p, CommRing (R p)] [∀ p, IsDomain (R p)]
    [∀ p, Algebra (R p) K] [∀ p, IsFractionRing (R p) K] where
  toRationalMap : RationalMapToProj K n
  is_morphism : toRationalMap.ExtendsMorphism R

theorem SmoothProjectiveCurve.rational_map_is_morphism
    {K : Type*} [Field K]
    {P : Type*}
    {n : ℕ}
    (φ : RationalMapToProj K n)
    (R : P → Type*)
    [∀ p, CommRing (R p)]
    [∀ p, IsDomain (R p)]
    [∀ p, IsDiscreteValuationRing (R p)]
    [∀ p, Algebra (R p) K]
    [∀ p, IsFractionRing (R p) K] :
    φ.ExtendsMorphism R :=
  fun p => φ.isRegularAt_of_isDVR (R p)

def SmoothProjectiveCurve.rational_map_extends_to_morphism
    {K : Type*} [Field K]
    {P : Type*}
    {n : ℕ}
    (φ : RationalMapToProj K n)
    (R : P → Type*)
    [∀ p, CommRing (R p)]
    [∀ p, IsDomain (R p)]
    [∀ p, IsDiscreteValuationRing (R p)]
    [∀ p, Algebra (R p) K]
    [∀ p, IsFractionRing (R p) K] :
    MorphismToProj K n R :=
  ⟨φ, SmoothProjectiveCurve.rational_map_is_morphism φ R⟩

structure RationalMapToProjectiveVariety (K : Type*) [Field K] (n : ℕ)
    (V : Set (Fin (n + 1) → K)) extends RationalMapToProj K n

def RationalMapToProjectiveVariety.IsMorphism {K : Type*} [Field K] {n : ℕ}
    {V : Set (Fin (n + 1) → K)}
    (φ : RationalMapToProjectiveVariety K n V)
    {P : Type*} (R : P → Type*)
    [∀ p, CommRing (R p)] [∀ p, IsDomain (R p)]
    [∀ p, Algebra (R p) K] [∀ p, IsFractionRing (R p) K] : Prop :=
  φ.toRationalMapToProj.ExtendsMorphism R

structure SmoothProjectiveCurveData (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra k K] (n : ℕ) where
  P : Type u
  R : P → Type u
  [instCR : ∀ p, CommRing (R p)]
  [instID : ∀ p, IsDomain (R p)]
  [instDVR : ∀ p, IsDiscreteValuationRing (R p)]
  [instAlg : ∀ p, Algebra (R p) K]
  [instFR : ∀ p, IsFractionRing (R p) K]
  [instAlgKR : ∀ p, Algebra k (R p)]
  [instScalarTower : ∀ p, IsScalarTower k (R p) K]
  emb : Fin (n + 1) → K
  emb_ne_zero : ∃ i, emb i ≠ 0
  n_pos : n ≥ 1
  emb_injective : Function.Injective emb
  point_nonempty : Nonempty P
  localRing_injective : ∀ (p₁ p₂ : P),
    (algebraMap (R p₁) K).range = (algebraMap (R p₂) K).range → p₁ = p₂
  localRing_surjective : ∀ (V : ValuationSubring K)
    [IsDiscreteValuationRing V] [IsFractionRing V K],
    ∃ p, (algebraMap (R p) K).range = V.toSubring

attribute [instance] SmoothProjectiveCurveData.instCR SmoothProjectiveCurveData.instID
  SmoothProjectiveCurveData.instDVR SmoothProjectiveCurveData.instAlg
  SmoothProjectiveCurveData.instFR SmoothProjectiveCurveData.instAlgKR
  SmoothProjectiveCurveData.instScalarTower

def DVRDominates {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    (φ_star : K₂ →+* K₁)
    (R₁ : Type*) [CommRing R₁] [IsDomain R₁] [Algebra R₁ K₁] [IsFractionRing R₁ K₁]
    (R₂ : Type*) [CommRing R₂] [IsDomain R₂] [Algebra R₂ K₂] [IsFractionRing R₂ K₂] : Prop :=
  ∀ x : K₂, IsLocalization.IsInteger R₂ x → IsLocalization.IsInteger R₁ (φ_star x)

def IsConstantFieldHom {k K₁ K₂ : Type*} [Field k] [Field K₁] [Field K₂]
    [Algebra k K₁] [Algebra k K₂] (φ_star : K₂ →ₐ[k] K₁) : Prop :=
  ∀ x : K₂, φ_star x ∈ Set.range (algebraMap k K₁)

def IsSurjectiveOnPoints {k K₁ K₂ : Type*} [Field k] [Field K₁] [Field K₂]
    [Algebra k K₁] [Algebra k K₂]
    (φ_star : K₂ →ₐ[k] K₁)
    {P₁ : Type*} (R₁ : P₁ → Type*)
    [∀ p, CommRing (R₁ p)] [∀ p, IsDomain (R₁ p)] [∀ p, Algebra (R₁ p) K₁]
    [∀ p, IsFractionRing (R₁ p) K₁]
    {P₂ : Type*} (R₂ : P₂ → Type*)
    [∀ p, CommRing (R₂ p)] [∀ p, IsDomain (R₂ p)] [∀ p, Algebra (R₂ p) K₂]
    [∀ p, IsFractionRing (R₂ p) K₂] : Prop :=
  ∀ p₂ : P₂, ∃ p₁ : P₁, DVRDominates φ_star.toRingHom (R₁ p₁) (R₂ p₂)

structure BiratIso
    {k K₁ K₂ : Type u} [Field k]
    [Field K₁] [Algebra k K₁] {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k K₁ n₁)
    [Field K₂] [Algebra k K₂] {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k K₂ n₂) where
  σ : K₁ ≃+* K₂
  forward : RationalMapToProj K₁ n₂
  backward : RationalMapToProj K₂ n₁
  forward_inverse : ∃ c₁ : K₁, c₁ ≠ 0 ∧
    ∀ i : Fin (n₁ + 1), σ.symm (backward.coords i) = c₁ * C₁.emb i
  backward_inverse : ∃ c₂ : K₂, c₂ ≠ 0 ∧
    ∀ i : Fin (n₂ + 1), σ (forward.coords i) = c₂ * C₂.emb i

structure CurveIso
    {k K₁ K₂ : Type u} [Field k]
    [Field K₁] [Algebra k K₁] {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k K₁ n₁)
    [Field K₂] [Algebra k K₂] {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k K₂ n₂) where
  σ : K₁ ≃+* K₂
  forward : RationalMapToProj K₁ n₂
  backward : RationalMapToProj K₂ n₁
  forward_regular : ∀ p, forward.IsRegularAt (C₁.R p)
  backward_regular : ∀ p, backward.IsRegularAt (C₂.R p)
  forward_inverse : ∃ c₁ : K₁, c₁ ≠ 0 ∧
    ∀ i : Fin (n₁ + 1), σ.symm (backward.coords i) = c₁ * C₁.emb i
  backward_inverse : ∃ c₂ : K₂, c₂ ≠ 0 ∧
    ∀ i : Fin (n₂ + 1), σ (forward.coords i) = c₂ * C₂.emb i

def SmoothProjectiveCurve.birational_map_is_isomorphism
    {k K₁ K₂ : Type u} [Field k]
    [Field K₁] [Algebra k K₁] {n₁ : ℕ} {C₁ : SmoothProjectiveCurveData k K₁ n₁}
    [Field K₂] [Algebra k K₂] {n₂ : ℕ} {C₂ : SmoothProjectiveCurveData k K₂ n₂}
    (Φ : BiratIso C₁ C₂) : CurveIso C₁ C₂ :=
  { σ := Φ.σ
    forward := Φ.forward
    backward := Φ.backward
    forward_regular :=
      @SmoothProjectiveCurve.rational_map_is_morphism K₁ _ C₁.P _ Φ.forward C₁.R _ _ _ _ _
    backward_regular :=
      @SmoothProjectiveCurve.rational_map_is_morphism K₂ _ C₂.P _ Φ.backward C₂.R _ _ _ _ _
    forward_inverse := Φ.forward_inverse
    backward_inverse := Φ.backward_inverse }

namespace FunctionField_k

variable {k : Type*} [Field k]
variable {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]

def localizationSubalgebraCarrier (S : Subalgebra k F) [IsFractionRing S F]
    (𝔭 : Ideal S) [𝔭.IsPrime] : Set F :=
  {x : F | ∃ (a : S) (b : 𝔭.primeCompl),
    x * algebraMap S F b.1 = algebraMap S F a}

section Lemma18_11_Helpers

def dvrSubalgebraToValuationSubring
    (R : Subalgebra k F) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] :
    ValuationSubring F where
  toSubring := R.toSubring
  mem_or_inv_mem' := by
    intro x
    haveI : ValuationRing R := of_isDiscreteValuationRing R
    rcases ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | ⟨a, ha⟩
    · left; show x ∈ (R : Set F); rw [← ha]; exact a.2
    · right; show x⁻¹ ∈ (R : Set F); rw [← ha]; exact a.2


instance dvrSubalgebraToValuationSubring_isDVR
    (R : Subalgebra k F) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] :
    IsDiscreteValuationRing (dvrSubalgebraToValuationSubring R) := by
  change IsDiscreteValuationRing R; infer_instance

structure DVROfFunctionField (k F : Type*) [Field k] [Field F] [Algebra k F] where
  valRing : ValuationSubring F
  contains_k : ∀ (a : k), algebraMap k F a ∈ valRing
  isDVR : IsDiscreteValuationRing valRing
  isFractionRing : IsFractionRing valRing F

attribute [instance] DVROfFunctionField.isDVR DVROfFunctionField.isFractionRing

def DVROfFunctionField.localRing (P : DVROfFunctionField k F) : ValuationSubring F :=
  P.valRing

def DVROfFunctionField.vanishesAt (P : DVROfFunctionField k F) (f : F) : Prop :=
  ∃ (hf : f ∈ P.valRing), ¬IsUnit (⟨f, hf⟩ : P.valRing)

def AbstractCurve.regularFunctions (U : Set (DVROfFunctionField k F)) : Subring F where
  carrier := {f : F | ∀ P ∈ U, f ∈ P.valRing}
  mul_mem' hf hg P hP := P.valRing.toSubring.mul_mem (hf P hP) (hg P hP)
  one_mem' P _ := P.valRing.toSubring.one_mem
  add_mem' hf hg P hP := P.valRing.toSubring.add_mem (hf P hP) (hg P hP)
  zero_mem' P _ := P.valRing.toSubring.zero_mem
  neg_mem' hf P hP := P.valRing.toSubring.neg_mem (hf P hP)

def AbstractCurve.zeroLocus (S : Set F) : Set (DVROfFunctionField k F) :=
  {P | ∀ f ∈ S, P.vanishesAt f}

instance AbstractCurve.zariskiTopology : TopologicalSpace (DVROfFunctionField k F) :=
  TopologicalSpace.generateFrom
    {U | ∃ (f : F), U = (AbstractCurve.zeroLocus ({f} : Set F))ᶜ}

structure AbstractCurve (k F : Type*) [Field k] [Field F] [Algebra k F] where
  finitelyGenerated : (⊤ : IntermediateField k F).FG
  transcendenceDegreeOne : ∃ (x : F), Transcendental k x ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) F
  algClosedInF : ∀ (x : F), IsAlgebraic k x → x ∈ (⊥ : IntermediateField k F)
  topology : TopologicalSpace (DVROfFunctionField k F) := AbstractCurve.zariskiTopology

@[reducible]
def AbstractCurve.toFunctionField_k {k F : Type*} [Field k] [Field F] [Algebra k F]
    (C : AbstractCurve k F) : FunctionField_k k F where
  finitelyGenerated := C.finitelyGenerated
  transcendenceDegreeOne := C.transcendenceDegreeOne
  algClosedInF := C.algClosedInF

def AbstractCurve.ofFunctionField_k (k F : Type*) [Field k] [Field F] [Algebra k F]
    [h : FunctionField_k k F] : AbstractCurve k F where
  finitelyGenerated := h.finitelyGenerated
  transcendenceDegreeOne := h.transcendenceDegreeOne
  algClosedInF := h.algClosedInF

structure AbstractCurveMorphism (k F₁ F₂ : Type*) [Field k] [Field F₁] [Field F₂]
    [Algebra k F₁] [Algebra k F₂] where
  toFun : DVROfFunctionField k F₁ → DVROfFunctionField k F₂
  pullback : F₂ →+* F₁
  pullback_comp : ∀ (a : k), pullback (algebraMap k F₂ a) = algebraMap k F₁ a
  pullback_regular : ∀ (P : DVROfFunctionField k F₁) (f : F₂),
    f ∈ (toFun P).valRing → pullback f ∈ P.valRing

noncomputable def SmoothProjectiveCurveData.pointValSubring
    {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P) :
    ValuationSubring K where
  toSubring := (algebraMap (C.R p) K).range
  mem_or_inv_mem' x := by
    haveI : ValuationRing (C.R p) := of_isDiscreteValuationRing (C.R p)
    rcases ValuationRing.isInteger_or_isInteger (C.R p) x with ⟨r, hr⟩ | ⟨r, hr⟩
    · left; exact ⟨r, hr⟩
    · right; exact ⟨r, hr⟩

noncomputable instance SmoothProjectiveCurveData.pointValSubring_isDVR
    {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P) :
    IsDiscreteValuationRing (C.pointValSubring p) := by
  have : IsDomain (C.pointValSubring p) := Subring.instIsDomainSubtypeMem _
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (RingEquiv.ofBijective
      ((algebraMap (C.R p) K).codRestrict (C.pointValSubring p).toSubring (fun r => ⟨r, rfl⟩))
      ⟨fun _ _ h => IsFractionRing.injective (C.R p) K (Subtype.ext_iff.mp h),
       fun ⟨_, r, rfl⟩ => ⟨r, rfl⟩⟩)

theorem SmoothProjectiveCurveData.contains_k
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P)
    (a : k) : algebraMap k K a ∈ C.pointValSubring p := by
  change ∃ a_1, (algebraMap (C.R p) K) a_1 = (algebraMap k K) a
  exact ⟨algebraMap k (C.R p) a, (IsScalarTower.algebraMap_apply k (C.R p) K a).symm⟩

noncomputable def SmoothProjectiveCurveData.pointToDVR
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P) : DVROfFunctionField k K where
  valRing := C.pointValSubring p
  contains_k := C.contains_k p
  isDVR := C.pointValSubring_isDVR p
  isFractionRing := inferInstance

def SmoothProjectiveCurveData.vanishesAt
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P) (f : K) : Prop :=
  ∃ (hf : f ∈ (C.pointValSubring p : Set K)),
    ¬IsUnit (⟨f, hf⟩ : C.pointValSubring p)

def SmoothProjectiveCurveData.zariskiTopology
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) : TopologicalSpace C.P :=
  TopologicalSpace.generateFrom
    {U | ∃ (f : K), U = {p | ¬C.vanishesAt p f}}

def SmoothProjectiveCurveData.regularFunctions
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) (U : Set C.P) : Set K :=
  {f : K | ∀ p ∈ U, f ∈ (C.pointValSubring p : Set K)}

structure AbstractCurveIsomorphism
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) where
  pointEquiv : C.P ≃ DVROfFunctionField k K
  localRing_compat : ∀ p, Set.range (algebraMap (C.R p) K) = ((pointEquiv p).valRing : Set K)
  forward_continuous : @Continuous C.P (DVROfFunctionField k K)
    C.zariskiTopology AbstractCurve.zariskiTopology pointEquiv

  regularFunctions_compat : ∀ (U : Set (DVROfFunctionField k K)),
    (AbstractCurve.regularFunctions U).carrier =
      C.regularFunctions (pointEquiv.symm '' U)

structure IsAbstractCurveIsomorphism
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n)
    (φ : C.P ≃ DVROfFunctionField k K) : Prop where
  localRing_eq : ∀ p, Set.range (algebraMap (C.R p) K) = ((φ p).valRing : Set K)
  regularFunctions_eq : ∀ (U : Set C.P) (f : K),
    f ∈ C.regularFunctions U ↔ f ∈ AbstractCurve.regularFunctions (φ '' U)

instance instIsDiscreteValuationRingSubtypeValuationSubring {K : Type*} [Field K]
    (p : { V : ValuationSubring K // IsDiscreteValuationRing V }) :
    IsDiscreteValuationRing ↥p.val := p.prop

def BiratIso.ofSameFunctionField
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k F n₁)
    {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k F n₂) :
    BiratIso C₁ C₂ where
  σ := RingEquiv.refl F
  forward := ⟨C₂.emb, C₂.emb_ne_zero⟩
  backward := ⟨C₁.emb, C₁.emb_ne_zero⟩
  forward_inverse := ⟨1, one_ne_zero, fun i => by simp [RingEquiv.refl_apply]⟩
  backward_inverse := ⟨1, one_ne_zero, fun i => by simp [RingEquiv.refl_apply]⟩

def unique_smooth_model_uniqueness
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k F n₁)
    {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k F n₂) :
    CurveIso C₁ C₂ :=
  SmoothProjectiveCurve.birational_map_is_isomorphism (BiratIso.ofSameFunctionField C₁ C₂)

end ArithmeticGeometry
