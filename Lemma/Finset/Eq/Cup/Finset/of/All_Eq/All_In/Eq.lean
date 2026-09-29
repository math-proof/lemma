import Mathlib.GroupTheory.Perm.Fin
import sympy.sets.sets
import sympy.Basic
open Nat


@[main]
private lemma main
  {n : ℕ}
  {S : Finset (Fin n → ℤ)}
  {e : Finset ℤ}
-- given
  (h₀ : ∀ x ∈ S, Finset.univ.image x = e)
  (h₁ : ∀ x ∈ S, ∀ p : Fin n → Fin n, Finset.univ.image p = Finset.univ → x ∘ p ∈ S)
  (h₂ : e.card = n)
  (h₃ : S.Nonempty) :
-- imply
  S.card = n ! := by
-- proof
  obtain ⟨x0, hx0⟩ := h₃
  have inj : ∀ x ∈ S, Function.Injective x := by
    intro x hx
    have hc : (Finset.univ.image x).card = (Finset.univ : Finset (Fin n)).card := by
      rw [h₀ x hx, h₂, Finset.card_univ, Fintype.card_fin]
    exact fun a b hab => Finset.card_image_iff.mp hc (Finset.mem_coe.mpr (Finset.mem_univ a)) (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
  have rng : ∀ x ∈ S, Set.range x = Set.range x0 := by
    intro x hx
    rw [← Set.image_univ, ← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image, ← Finset.coe_image, h₀ x hx, h₀ x0 hx0]
  let F : Equiv.Perm (Fin n) → Fin n → ℤ := fun σ => x0 ∘ σ
  have hF : Function.Injective F := by
    intro σ τ hst
    exact Equiv.ext fun i => inj x0 hx0 (congrFun hst i)
  have hS : S = Finset.univ.image F := by
    ext x
    rw [Finset.mem_image]
    constructor
    · intro hx
      refine ⟨(Equiv.ofInjective x (inj x hx)).trans ((Equiv.setCongr (rng x hx)).trans (Equiv.ofInjective x0 (inj x0 hx0)).symm),
        Finset.mem_univ _, ?_⟩
      funext i
      simp only [F, Function.comp_apply, Equiv.trans_apply]
      rw [Equiv.apply_ofInjective_symm (inj x0 hx0)]
      simp
    · rintro ⟨σ, -, rfl⟩
      exact h₁ x0 hx0 σ (Finset.image_univ_of_surjective σ.surjective)
  rw [hS, Finset.card_image_of_injective _ hF, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]


-- created on 2026-09-27
