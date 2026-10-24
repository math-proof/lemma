import Mathlib
import Lemma.Definitions.Def_ModularCurve_LaurentCoeff
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Lemma.Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve

def realizeOf (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) (τ : ℍ) : ℂ := by
  classical
  exact
    if H : ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
    else 0

theorem realizeOf_def (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) (τ : ℍ) :
    realizeOf Γ x τ = by
      classical
      exact
        if H : ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
            (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
              x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
                ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
        then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
        else 0 :=
  rfl

theorem realizeOf_of_not (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) (τ : ℍ)
    (h : ¬ ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    realizeOf Γ x τ = 0 := by
  classical
  rw [realizeOf_def]
  exact dif_neg h

structure ComplexPlaceDictionaryOf (Γ : Subgroup SL(2, ℤ))
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) where

  pt : ℍ → AlgebraicCurve.Place ℂ (laurentBaseChange ℂ F₀)

  ramification : ℍ → ℕ

  ramification_pos : ∀ τ : ℍ, 0 < ramification τ

  pt_smul : ∀ (γ : Γ) (τ : ℍ), pt ((γ : SL(2, ℤ)) • τ) = pt τ

  mem_pt_iff : ∀ (τ : ℍ) (x : laurentBaseChange ℂ F₀),
    x ∈ (pt τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
        (fun z : ℍ => ‖realizeOf Γ (x : LaurentSeries ℂ) z‖)

  meromorphicOrderAt_realizeOf : ∀ (τ : ℍ) (x : laurentBaseChange ℂ F₀), x ≠ 0 →
    meromorphicOrderAt (fun z : ℂ => realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) =
      (((ramification τ : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)

namespace ComplexPlaceDictionaryOf

variable {Γ : Subgroup SL(2, ℤ)} {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

theorem pt_smul_of_mem (D : ComplexPlaceDictionaryOf Γ F₀) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    D.pt (γ • τ) = D.pt τ :=
  D.pt_smul ⟨γ, hγ⟩ τ

theorem ramification_ne_zero (D : ComplexPlaceDictionaryOf Γ F₀) (τ : ℍ) : D.ramification τ ≠ 0 :=
  (D.ramification_pos τ).ne'

end ComplexPlaceDictionaryOf

theorem realizeOf_gamma0 (N : ℕ) (x : LaurentSeries ℂ) (τ : ℍ) :
    realizeOf (CongruenceSubgroup.Gamma0 N) x τ = realize N x τ :=
  rfl

def ComplexPlaceDictionaryOf.ofGamma0 {N : ℕ} [NeZero N] (D : ComplexPlaceDictionary N) :
    ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma0 N) (modularFunctionFieldFull N) where
  pt := D.pt
  ramification := D.ramification
  ramification_pos := D.ramification_pos
  pt_smul := D.pt_smul
  mem_pt_iff := D.mem_pt_iff
  meromorphicOrderAt_realizeOf := D.meromorphicOrderAt_realize

def ComplexPlaceDictionaryOf.toGamma0 {N : ℕ} [NeZero N]
    (D : ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma0 N) (modularFunctionFieldFull N)) :
    ComplexPlaceDictionary N where
  pt := D.pt
  ramification := D.ramification
  ramification_pos := D.ramification_pos
  pt_smul := D.pt_smul
  mem_pt_iff := D.mem_pt_iff
  meromorphicOrderAt_realize := D.meromorphicOrderAt_realizeOf

@[simp]
theorem ComplexPlaceDictionaryOf.pt_ofGamma0 {N : ℕ} [NeZero N] (D : ComplexPlaceDictionary N) :
    (ComplexPlaceDictionaryOf.ofGamma0 D).pt = D.pt :=
  rfl

@[simp]
theorem ComplexPlaceDictionaryOf.pt_toGamma0 {N : ℕ} [NeZero N]
    (D : ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma0 N) (modularFunctionFieldFull N)) :
    D.toGamma0.pt = D.pt :=
  rfl

end ModularCurve

end
