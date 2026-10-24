import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Meromorphic.Order
import Lemma.Definitions.Def_ModularCurve_X0
import Lemma.Definitions.Def_ModularCurve_LaurentCoeff
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve

def realize (N : ℕ) (x : LaurentSeries ℂ) (τ : ℍ) : ℂ := by
  classical
  exact
    if H : ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
          ModularForm (CongruenceSubgroup.Gamma0 N) k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
    else 0

structure ComplexPlaceDictionary (N : ℕ) [NeZero N] where

  pt : ℍ → AlgebraicCurve.Place ℂ (laurentBaseChange ℂ (modularFunctionFieldFull N))

  ramification : ℍ → ℕ

  ramification_pos : ∀ τ : ℍ, 0 < ramification τ

  pt_smul : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), pt ((γ : SL(2, ℤ)) • τ) = pt τ

  mem_pt_iff : ∀ (τ : ℍ) (x : laurentBaseChange ℂ (modularFunctionFieldFull N)),
    x ∈ (pt τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realize N (x : LaurentSeries ℂ) z‖)

  meromorphicOrderAt_realize : ∀ (τ : ℍ) (x : laurentBaseChange ℂ (modularFunctionFieldFull N)),
    x ≠ 0 →
      meromorphicOrderAt (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) =
        (((ramification τ : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)

end ModularCurve

end
