import Mathlib
import Lemma.ModularCurve.LaurentCoeff
import Class.AlgebraicCurve_DivisorClassGroup
import Def.ModularCurve_ComplexPlaceDictionary
import Structure.ModularCurve_ComplexPlaceDictionaryOf

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve


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
