import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {A : Type w} [CommRing A] [Algebra R A]
  {M : Subalgebra R A}
-- given
  (P : Subalgebra R A → Prop)
  (hsup : ∀ S S', P S → P S' → P (S ⊔ S'))
  (h : IsNoetherian R M)
  (hle : ∀ S, P S → S ≤ M)
  (h0 : ∃ S, P S) :
-- imply
  ∃ S, P S ∧ ∀ S', P S' → S' ≤ S := by
-- proof
  classical

  let F : {S : Subalgebra R A // P S} → Submodule R M := fun S =>
    Submodule.comap M.val.toLinearMap (Subalgebra.toSubmodule S.1)
  obtain ⟨S₀, hS₀⟩ := h0
  have hne : (Set.range F).Nonempty := ⟨F ⟨S₀, hS₀⟩, ⟨⟨S₀, hS₀⟩, rfl⟩⟩
  obtain ⟨N, ⟨⟨S, hS⟩, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr h (Set.range F) hne
  refine ⟨S, hS, fun S' hS' => ?_⟩

  have hsup : P (S ⊔ S') := hsup S S' hS hS'
  have hFle : F ⟨S, hS⟩ ≤ F ⟨S ⊔ S', hsup⟩ := by
    intro m hm
    exact (le_sup_left : S ≤ S ⊔ S') hm
  have hEq : F ⟨S ⊔ S', hsup⟩ = F ⟨S, hS⟩ :=
    (hFle.eq_or_lt.resolve_right (hmax (F ⟨S ⊔ S', hsup⟩) ⟨⟨S ⊔ S', hsup⟩, rfl⟩)).symm
  intro x hx
  have hxM : x ∈ M := hle (S ⊔ S') hsup ((le_sup_right : S' ≤ S ⊔ S') hx)
  have hx' : (⟨x, hxM⟩ : M) ∈ F ⟨S ⊔ S', hsup⟩ := (le_sup_right : S' ≤ S ⊔ S') hx
  rw [hEq] at hx'
  exact hx'


-- created on 2026-10-05
