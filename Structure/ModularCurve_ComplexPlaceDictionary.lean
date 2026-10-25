import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Meromorphic.Order
import Structure.ModularCurve_X0
import Def.ModularCurve_LaurentCoeff
import Class.AlgebraicCurve_DivisorClassGroup
import Def.ModularCurve_ComplexPlaceDictionary

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve


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
