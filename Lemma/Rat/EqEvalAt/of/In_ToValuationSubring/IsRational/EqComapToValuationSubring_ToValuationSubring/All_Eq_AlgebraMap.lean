import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.AlgebraicCurve_PlaceEvaluation
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open AlgebraicCurve
open Int


/--
[AlgebraicCurve_Place_evalAt_map_eq_of_comap_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_evalAt_map_eq_of_comap_eq.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  {τ : K →+* K'}
  {φ : F →+* F'}
  {v : Place K F}
  {v' : Place K' F'}
  {x : F}
-- given
  (hφ : ∀ c : K, φ (algebraMap K F c) = algebraMap K' F' (τ c))
  (h : v'.toValuationSubring.comap φ = v.toValuationSubring)
  (hv : v.IsRational)
  (hx : x ∈ v.toValuationSubring) :
-- imply
  v'.evalAt (φ x) = τ (v.evalAt x) := by
  have hmem : ∀ y : F, y ∈ v.toValuationSubring ↔ φ y ∈ v'.toValuationSubring := fun y ↦ by
    rw [← h, ValuationSubring.mem_comap]
  have hmax : ∀ (y : F) (hy : y ∈ v.toValuationSubring),
      (⟨y, hy⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring →
      (⟨φ y, (hmem y).1 hy⟩ : v'.toValuationSubring) ∈ IsLocalRing.maximalIdeal v'.toValuationSubring := by
-- proof
    intro y hy hyM
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hyM ⊢
    intro hu
    apply hyM
    obtain ⟨u, hu⟩ := hu
    have hy0 : φ y ≠ 0 := by
      intro h0
      have : (u : v'.toValuationSubring) = 0 := Subtype.ext (by rwa [hu])
      exact u.ne_zero this
    have hinv' : (φ y)⁻¹ ∈ v'.toValuationSubring := by
      have e : ((u⁻¹ : (v'.toValuationSubring)ˣ) : v'.toValuationSubring).1 = (φ y)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        have := congrArg (fun z : v'.toValuationSubring ↦ (z : F')) u.inv_mul
        simpa [hu] using this
      refine e ▸ ((u⁻¹ : (v'.toValuationSubring)ˣ) : v'.toValuationSubring).2
    have hinv : y⁻¹ ∈ v.toValuationSubring := (hmem _).2 (by rwa [map_inv₀])
    have hy0' : y ≠ 0 := fun h0 ↦ hy0 (by rw [h0, map_zero])
    refine ⟨⟨⟨y, hy⟩, ⟨y⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hy0'), Subtype.ext (inv_mul_cancel₀ hy0')⟩, rfl⟩
  set a : K := v.evalAt x with ha
  have hres : IsLocalRing.residue v.toValuationSubring ⟨x, hx⟩ = algebraMap K v.ResidueField a := (v.algebraMap_evalAt hv hx).symm
  have hdiff : (⟨x, hx⟩ - algebraMap K v.toValuationSubring a : v.toValuationSubring)
    ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_eq_zero]
    rfl
  have hxa : x - algebraMap K F a ∈ v.toValuationSubring :=
    sub_mem hx (v.algebraMap_mem' a)
  have hdiff1 : (⟨x - algebraMap K F a, hxa⟩ : v.toValuationSubring)
    ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    convert hdiff using 1
    rfl
  have hdiff' := hmax _ hxa hdiff1
  have hφx : φ x ∈ v'.toValuationSubring := (hmem x).1 hx
  have hφxa : (⟨φ x, hφx⟩ - algebraMap K' v'.toValuationSubring (τ a) : v'.toValuationSubring)
    ∈ IsLocalRing.maximalIdeal v'.toValuationSubring := by
    convert hdiff' using 1
    apply Subtype.ext
    simp [map_sub, hφ]
  have hres' : IsLocalRing.residue v'.toValuationSubring ⟨φ x, hφx⟩ = algebraMap K' v'.ResidueField (τ a) := by
    rwa [← sub_eq_zero, IsScalarTower.algebraMap_apply K' v'.toValuationSubring v'.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  rw [v'.evalAt_of_mem hφx, hres', v'.residueInv_algebraMap]


-- created on 2026-10-24
