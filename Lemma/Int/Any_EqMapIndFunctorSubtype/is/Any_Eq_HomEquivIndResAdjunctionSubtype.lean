import Mathlib
import sympy.Basic

open CategoryTheory

/--
[Rep_exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv.lean)
-/
@[path]
private lemma main
  [Group G]
  {H : Subgroup G}
  {R₀ P₀ : Rep ℤ ↥H}
  {f₀ : R₀ ⟶ P₀}
  {C : Rep ℤ G}
  {φ : (Rep.indFunctor ℤ H.subtype).obj R₀ ⟶ C} :
-- imply
  (∃ χ : (Rep.indFunctor ℤ H.subtype).obj P₀ ⟶ C, (Rep.indFunctor ℤ H.subtype).map f₀ ≫ χ = φ) ↔
      ∃ χ₀ : P₀ ⟶ Rep.res H.subtype C, f₀ ≫ χ₀ = (Rep.indResAdjunction ℤ H.subtype).homEquiv R₀ C φ := by
-- proof
  constructor
  · rintro ⟨χ, rfl⟩
    exact ⟨(Rep.indResAdjunction ℤ H.subtype).homEquiv P₀ C χ,
      ((Rep.indResAdjunction ℤ H.subtype).homEquiv_naturality_left f₀ χ).symm⟩
  · rintro ⟨χ₀, h⟩
    refine ⟨((Rep.indResAdjunction ℤ H.subtype).homEquiv P₀ C).symm χ₀, ?_⟩
    apply ((Rep.indResAdjunction ℤ H.subtype).homEquiv R₀ C).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, h]


-- created on 2026-10-05
