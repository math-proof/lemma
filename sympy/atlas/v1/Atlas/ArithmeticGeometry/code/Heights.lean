/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.GaloisPlaceHelper
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisPlaceHelper

noncomputable section

open Height MvPolynomial

namespace AbsoluteHeight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Empty.Finite ι]

def absoluteHeight (P : Projectivization K (ι → K)) : ℝ :=
  Projectivization.mulHeight P


def logHeight (P : Projectivization K (ι → K)) : ℝ :=
  Real.log (absoluteHeight P)

theorem NumberField.FinitePlace.isFinitePlace_comp_galois {K : Type*} [Field K] [NumberField K]
    (σ : K ≃ₐ[ℚ] K) (v : NumberField.FinitePlace K) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      place (NumberField.FinitePlace.embedding w) =
        v.val.comp (f := (σ.symm : K →+* K)) σ.symm.injective := by
  let p := v.maximalIdeal
  let e : (NumberField.RingOfIntegers K) ≃+* (NumberField.RingOfIntegers K) :=
    NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv
  let w := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e p

  have habsN : Ideal.absNorm w.asIdeal = Ideal.absNorm p.asIdeal := by
    have hasideal : w.asIdeal =
        Ideal.comap (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          p.asIdeal := by
      show (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = _
      rw [IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv_apply,
          IsDedekindDomain.HeightOneSpectrum.comap_asIdeal]
    rw [hasideal, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot, Submodule.cardQuot]
    have h : p.asIdeal =
        (Ideal.comap (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          p.asIdeal).map
          (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) :=
      (Ideal.map_comap_of_surjective
        (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
        e.symm.surjective p.asIdeal).symm
    exact Nat.card_congr (Ideal.quotientEquiv _ p.asIdeal e.symm h).toEquiv
  use w
  apply AbsoluteValue.ext; intro x
  show ‖NumberField.FinitePlace.embedding w x‖ = v.val (σ.symm x)
  have hv : v = NumberField.FinitePlace.mk p :=
    (NumberField.FinitePlace.mk_maximalIdeal v).symm
  conv_rhs => rw [hv]
  show ‖NumberField.FinitePlace.embedding w x‖ =
    ‖NumberField.FinitePlace.embedding p (σ.symm x)‖
  rw [NumberField.FinitePlace.norm_embedding', NumberField.FinitePlace.norm_embedding']

  have hval : w.valuation K x = p.valuation K (σ.symm x) := by
    obtain ⟨a, b, hb, rfl⟩ :=
      IsFractionRing.div_surjective (NumberField.RingOfIntegers K) x
    simp only [map_div₀]
    congr 1 <;> {
      rw [show σ.symm (algebraMap (NumberField.RingOfIntegers K) K _) =
            algebraMap (NumberField.RingOfIntegers K) K (e.symm _) from by
        change σ.symm (_ : K) =
          ((NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm _ : K)
        rw [NumberField.RingOfIntegers.mapRingEquiv_symm_apply]; rfl,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact (intValuation_equivOfRingEquiv e p _).symm }
  rw [hval]
  simp only [habsN]

noncomputable def galoisEquivFinitePlace {K : Type*} [Field K] [NumberField K]
    (σ : K ≃ₐ[ℚ] K) : NumberField.FinitePlace K ≃ NumberField.FinitePlace K where
  toFun v := ⟨v.val.comp (f := (σ.symm : K →+* K)) σ.symm.injective,
    NumberField.FinitePlace.isFinitePlace_comp_galois σ v⟩
  invFun v := ⟨v.val.comp (f := (σ : K →+* K)) σ.injective, by
    have h := NumberField.FinitePlace.isFinitePlace_comp_galois σ⁻¹ v
    simp only [show (σ⁻¹ : K ≃ₐ[ℚ] K) = σ.symm from by ext; rfl,
      AlgEquiv.symm_symm] at h
    exact h⟩
  left_inv v := by
    apply Subtype.ext; apply AbsoluteValue.ext; intro x
    show v (σ.symm (σ x)) = v x
    rw [AlgEquiv.symm_apply_apply]
  right_inv v := by
    apply Subtype.ext; apply AbsoluteValue.ext; intro x
    show v (σ (σ.symm x)) = v x
    rw [AlgEquiv.apply_symm_apply]

structure TwoIsogenyData (W : WeierstrassCurve ℚ) [W.IsElliptic] where
  E'Points : Type
  instAddCommGroup : AddCommGroup E'Points
  phi : W.toAffine.Point →+ E'Points
  phi_hat : E'Points →+ W.toAffine.Point
  comp_eq : phi_hat.comp phi = zsmulAddGroupHom (2 : ℤ)
  descentTarget : Type
  instDescentTargetGroup : AddCommGroup descentTarget
  descentMap : E'Points →+ descentTarget
  descentMap_range_finite : Empty.Finite descentMap.range
  descentMap_ker_eq : descentMap.ker = phi.range
  descentTarget' : Type
  instDescentTarget'Group : AddCommGroup descentTarget'
  descentMap' : W.toAffine.Point →+ descentTarget'
  descentMap'_range_finite : Empty.Finite descentMap'.range
  descentMap'_ker_eq : descentMap'.ker = phi_hat.range
  phi_hat_ker_le_phi_range : phi_hat.ker ≤ phi.range

attribute [instance] TwoIsogenyData.instAddCommGroup
attribute [instance] TwoIsogenyData.instDescentTargetGroup
attribute [instance] TwoIsogenyData.instDescentTarget'Group
attribute [instance] TwoIsogenyData.descentMap_range_finite
attribute [instance] TwoIsogenyData.descentMap'_range_finite

def IsNonzeroSquare (q : ℚ) : Prop := ∃ r : ℚ, r ≠ 0 ∧ q = r ^ 2


def E'Curve (a b : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0; a₂ := -2 * a; a₃ := 0; a₄ := a ^ 2 - 4 * b; a₆ := 0

noncomputable def descentMapRaw (a b : ℚ) (hdisc : a ^ 2 - 4 * b ≠ 0) :
    (E'Curve a b).toAffine.Point → Additive (ℚˣ ⧸ Subgroup.square ℚˣ) :=
  fun P => match P with
  | .zero => Additive.ofMul 1
  | .some x _y _hxy =>
    if hx : x = 0 then
      Additive.ofMul (QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (a ^ 2 - 4 * b) hdisc))
    else
      Additive.ofMul (QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 x hx))

def canonicalHeightSeq (h : E → ℝ) (P : E) (n : ℕ) : ℝ :=
  h ((2 ^ n : ℤ) • P) / (4 : ℝ) ^ n

def canonicalHeight (h : E → ℝ) (P : E) : ℝ :=
  limUnder atTop (canonicalHeightSeq h P)

structure IsWeilHeightOnCurve (h : W.toAffine.Point → ℝ) : Prop where
  doubling_bound : ∃ C : ℝ, ∀ P : W.toAffine.Point,
    |h ((2 : ℤ) • P) - 4 * h P| ≤ C
  height_nonneg_zero : 0 ≤ h 0
  northcott : ∀ B : ℝ, {P : W.toAffine.Point | h P ≤ B}.Finite

def EllipticCurve.NeronTateHeight (h : W.toAffine.Point → ℝ)
    (_hWeil : IsWeilHeightOnCurve W h) (P : W.toAffine.Point) : ℝ :=
  canonicalHeight h P


set_option linter.unusedSectionVars false in

end EllipticCurveCanonicalHeight

namespace TateTheorem

def tateSeq {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (x : S) (n : ℕ) : ℝ :=
  h (φ^[n] x) / r ^ n


noncomputable def mapCoords {K L : Type*} [CommRing K] [CommRing L]
    (σ : K →+* L) (n : ℕ) :
    (Fin (n + 1) → K) →ₛₗ[σ] (Fin (n + 1) → L) where
  toFun v i := σ (v i)
  map_add' x y := by ext i; simp [map_add]
  map_smul' c x := by ext i; simp [RingHom.map_mul]

def IsProjectiveMorphism {K : Type*} [CommRing K] {n m : ℕ} (d : ℕ)
    (φ : Fin (m + 1) → MvPolynomial (Fin (n + 1)) K) : Prop :=
  (∀ i, (φ i).IsHomogeneous d) ∧
  (∀ x : Fin (n + 1) → K, x ≠ 0 → ∃ i, MvPolynomial.eval x (φ i) ≠ 0)

variable {K : Type*} [Field K] [NumberField K]
variable {n m : ℕ}
