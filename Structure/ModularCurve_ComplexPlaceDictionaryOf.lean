import Mathlib
import Def.ModularCurve_LaurentCoeff
import Class.AlgebraicCurve_DivisorClassGroup
import Structure.ModularCurve_ComplexPlaceDictionary

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


end ComplexPlaceDictionaryOf


end ModularCurve

end
