/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace SimpleGroups

open Matrix

@[reducible] def lieAlgebraMatrix (n : ℕ) :
    LieAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) := inferInstance

noncomputable def lieAlgebraSet (m : ℕ) (G : Subgroup (GeneralLinearGroup (Fin m) ℝ)) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | ∀ t : ℝ, ∃ u : (Matrix (Fin m) (Fin m) ℝ)ˣ,
    (u : Matrix (Fin m) (Fin m) ℝ) = NormedSpace.exp (t • A) ∧ u ∈ G}

noncomputable def lieAlgebraSetPath (m : ℕ) (G : Subgroup (GeneralLinearGroup (Fin m) ℝ)) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | ∃ (ε : ℝ) (_ : ε > 0) (f : ℝ → Matrix (Fin m) (Fin m) ℝ),
    DifferentiableAt ℝ f 0 ∧
    f 0 = 1 ∧
    deriv f 0 = A ∧
    (∀ t : ℝ, |t| < ε → ∃ u : (Matrix (Fin m) (Fin m) ℝ)ˣ,
      (u : Matrix (Fin m) (Fin m) ℝ) = f t ∧ u ∈ G)}

open DualNumber in
noncomputable def lieAlgebraSetDual (m : ℕ)
    (P : Matrix (Fin m) (Fin m) ℝ[ε] → Prop) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | P ((1 : Matrix (Fin m) (Fin m) ℝ[ε]) + A.map (TrivSqZeroExt.inr))}


open DualNumber in
structure IsOneParameterGroup (m : ℕ) (φ : ℝ → Matrix (Fin m) (Fin m) ℂ) : Prop where
  map_zero : φ 0 = 1
  map_add : ∀ s t : ℝ, φ (s + t) = φ s * φ t
  differentiable : Differentiable ℝ φ

section OneParamSubgroupTheorem
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

noncomputable def diagRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (↑θ * Complex.I), (0:ℂ); 0, Complex.exp (-(↑θ * Complex.I))]

lemma diagRotation_add (θ₁ θ₂ : ℝ) :
    diagRotation θ₁ * diagRotation θ₂ = diagRotation (θ₁ + θ₂) := by
  simp only [diagRotation]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  · ring_nf
  · ring_nf

lemma diagRotation_zero : diagRotation 0 = 1 := by
  simp only [diagRotation]
  ext i j; fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 800000 in
lemma diagRotation_mem_SU2 (θ : ℝ) : diagRotation θ ∈ SU2 := by
  simp only [diagRotation, Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
  have hconj1 : starRingEnd ℂ (Complex.exp (↑θ * Complex.I)) =
      Complex.exp (-(↑θ * Complex.I)) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, Complex.conj_I]
  have hconj2 : starRingEnd ℂ (Complex.exp (-(↑θ * Complex.I))) =
      Complex.exp (↑θ * Complex.I) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, Complex.conj_I]
  have hconj_struct : ∀ z : ℂ, ({ re := z.re, im := -z.im } : ℂ) = starRingEnd ℂ z := by
    intro z; apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          mul_zero, add_zero, zero_add, Matrix.one_apply,
          Fin.isValue, ite_true, ite_false, Fin.reduceFinMk, Fin.reduceEq,
          Matrix.transpose_apply]
    · rw [hconj_struct, hconj1, ← Complex.exp_add]; simp
    · apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
    · rw [hconj_struct, hconj2, ← Complex.exp_add]; simp
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          zero_mul, add_zero, zero_add, Matrix.one_apply,
          Fin.isValue, ite_true, ite_false, Fin.reduceFinMk, Fin.reduceEq,
          Matrix.transpose_apply]
    · rw [hconj_struct, hconj1, ← Complex.exp_add]; simp
    · apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
    · rw [hconj_struct, hconj2, ← Complex.exp_add]; simp
  · simp [Matrix.det_fin_two, ← Complex.exp_add]

noncomputable def longitudeI : Subgroup SU2 where
  carrier := {M | ∃ θ : ℝ, M.val = diagRotation θ}
  mul_mem' := by
    intro a b ⟨θ₁, hθ₁⟩ ⟨θ₂, hθ₂⟩
    exact ⟨θ₁ + θ₂, by
      change (a * b).val = diagRotation (θ₁ + θ₂)
      change a.val * b.val = diagRotation (θ₁ + θ₂)
      rw [hθ₁, hθ₂, diagRotation_add]⟩
  one_mem' := ⟨0, by show (1 : SU2).val = diagRotation 0; simp [diagRotation_zero]⟩
  inv_mem' := by
    intro a ⟨θ, hθ⟩
    refine ⟨-θ, ?_⟩
    have hinv : a⁻¹ = ⟨diagRotation (-θ), diagRotation_mem_SU2 (-θ)⟩ := by
      have h : ⟨diagRotation (-θ), diagRotation_mem_SU2 (-θ)⟩ * a = 1 := by
        ext1
        show diagRotation (-θ) * a.val = 1
        rw [hθ, diagRotation_add]; simp [diagRotation_zero]
      exact (mul_eq_one_iff_eq_inv.mp h).symm
    show a⁻¹.val = diagRotation (-θ)
    rw [hinv]

lemma diagRotation_periodic (θ : ℝ) (n : ℤ) :
    diagRotation (θ + n * (2 * Real.pi)) = diagRotation θ := by
  simp only [diagRotation]
  ext i j; fin_cases i <;> fin_cases j <;> simp
  · have h : (↑θ + ↑n * (2 * (↑Real.pi : ℂ))) * Complex.I =
        ↑θ * Complex.I + ↑n * (2 * ↑Real.pi * Complex.I) := by ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · have h : -((↑θ + ↑n * (2 * (↑Real.pi : ℂ))) * Complex.I) =
        -(↑θ * Complex.I) + (-(↑n : ℂ)) * (2 * ↑Real.pi * Complex.I) := by ring
    rw [h, Complex.exp_add]
    rw [show -(↑n : ℂ) * (2 * ↑Real.pi * Complex.I) = ↑(-n) * (2 * ↑Real.pi * Complex.I) from by push_cast; ring]
    rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]

noncomputable def diagRotationToLongI (θ : ℝ) : longitudeI :=
  ⟨⟨diagRotation θ, diagRotation_mem_SU2 θ⟩, ⟨θ, rfl⟩⟩

lemma diagRotationToLongI_periodic (a b : ℝ)
    (h : @Setoid.r _ (QuotientAddGroup.leftRel (AddSubgroup.zmultiples (2 * Real.pi))) a b) :
    diagRotationToLongI a = diagRotationToLongI b := by
  simp only [QuotientAddGroup.leftRel_apply] at h
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  simp only [diagRotationToLongI]
  ext1; ext1
  show diagRotation a = diagRotation b
  have hba : b = a + n * (2 * Real.pi) := by
    have := hn; simp [zsmul_eq_mul] at this; linarith
  rw [hba, diagRotation_periodic]

noncomputable def longitudeMap : Multiplicative (AddCircle (2 * Real.pi)) →* longitudeI where
  toFun x := Quotient.lift diagRotationToLongI
    diagRotationToLongI_periodic (Multiplicative.toAdd x)
  map_one' := by
    show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
      (0 : AddCircle (2 * Real.pi)) = 1
    show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
      (QuotientAddGroup.mk 0) = 1
    simp only [Quotient.lift_mk, diagRotationToLongI]
    ext1; ext1
    exact diagRotation_zero
  map_mul' x y := by
    show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
      (Multiplicative.toAdd x + Multiplicative.toAdd y) =
      Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (Multiplicative.toAdd x) *
      Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (Multiplicative.toAdd y)
    induction Multiplicative.toAdd x using Quotient.inductionOn with
    | h a =>
      induction Multiplicative.toAdd y using Quotient.inductionOn with
      | h b =>
        show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
          (QuotientAddGroup.mk a + QuotientAddGroup.mk b) =
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk a) *
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk b)
        change Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
          (QuotientAddGroup.mk (a + b)) =
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk a) *
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk b)
        simp only [Quotient.lift_mk, diagRotationToLongI]
        ext1; ext1
        exact (diagRotation_add a b).symm
def SL2.HasEigenvalues (M : Matrix.SpecialLinearGroup (Fin 2) F) (s : F) : Prop :=
  (↑M : Matrix (Fin 2) (Fin 2) F).charpoly =
    (Polynomial.X - Polynomial.C s) * (Polynomial.X - Polynomial.C s⁻¹)

def SL2.IsConjToDiag (M : Matrix.SpecialLinearGroup (Fin 2) F) (s : F) : Prop :=
  ∃ P : Matrix.SpecialLinearGroup (Fin 2) F,
    (P * M * P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 = Matrix.diagonal ![s, s⁻¹]
