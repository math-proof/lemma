import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_CerednikDrinfeld_GradedCartierNModule
open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData


/--
[CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {R B' : Type} [CommRing R] [CommRing B']
  {jR : CerednikDrinfeld.Zp2 p →+* R}
  {j' : CerednikDrinfeld.Zp2 p →+* B'}
  {φ : R →+* B'}
  {D : CerednikDrinfeld.GradedCartierModuleData p R jR}
  {D' : CerednikDrinfeld.GradedCartierModuleData p B' j'}
  {γ : Fin 2 → D.M}
  {δ₁ δ₂ : D.M →+ D'.M}
-- given
  (hD' : D'.IsSpecialCartierModule)
  (hγ : D.IsHomogeneousVBasis γ)
  (h₀ : ∀ (w : WittVector p R) (x : D.M), δ₁ (w • x) = WittVector.map φ w • δ₁ x)
  (h₁V : ∀ x : D.M, δ₁ (D.verschiebung x) = D'.verschiebung (δ₁ x))
  (h₁ : ∀ (w : WittVector p R) (x : D.M), δ₂ (w • x) = WittVector.map φ w • δ₂ x)
  (h₂V : ∀ x : D.M, δ₂ (D.verschiebung x) = D'.verschiebung (δ₂ x))
  (hγeq : ∀ i : Fin 2, δ₁ (γ i) = δ₂ (γ i)) :
-- imply
  δ₁ = δ₂ := by
-- proof
  classical
  have hit0 : ∀ N : ℕ, Nat.iterate (⇑D'.verschiebung) N (0 : D'.M) = 0 := by
    intro N
    induction N with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]
  set δ : D.M →+ D'.M := δ₁ - δ₂ with hδ
  have hδγ : ∀ i, δ (γ i) = 0 := fun i => by
    simp only [hδ, AddMonoidHom.sub_apply, hγeq, sub_self]
  have hδs : ∀ (w : WittVector p R) (x : D.M), δ (w • x) = WittVector.map φ w • δ x := fun w x => by
    simp only [hδ, AddMonoidHom.sub_apply, h₀, h₁, smul_sub]
  have hδV : ∀ x, δ (D.verschiebung x) = D'.verschiebung (δ x) := fun x => by
    simp only [hδ, AddMonoidHom.sub_apply, h₁V, h₂V, map_sub]
  have key : ∀ (N : ℕ) (x : D.M), ∃ t : D'.M, δ x = Nat.iterate (⇑D'.verschiebung) N t := by
    intro N
    induction N with
    | zero =>
      intro x
      exact ⟨δ x, rfl⟩
    | succ n ih =>
      intro x
      obtain ⟨⟨c, y⟩, hx, -⟩ := hγ.2 x
      obtain ⟨t, ht⟩ := ih y
      refine ⟨t, ?_⟩
      rw [hx, map_add, map_sum, hδV, ht, Function.iterate_succ_apply']
      have : ∑ i, δ (WittVector.teichmuller p (c i) • γ i) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [hδs, hδγ, smul_zero]
      rw [this, zero_add]
  have hsep : ∀ x, δ x = 0 := by
    intro x
    obtain ⟨s, hs, huniq⟩ := hD'.2 (fun _ => (0 : D'.M))
    have hz : (0 : D'.M) = s := huniq 0 (fun N => ⟨0, by rw [hit0, Finset.sum_eq_zero (fun m _ => hit0 m), add_zero]⟩)
    have hd : δ x = s := huniq (δ x) (fun N => by
      obtain ⟨t, ht⟩ := key N x
      exact ⟨t, by rwa [Finset.sum_eq_zero (fun m _ => hit0 m), zero_add]⟩)
    rw [hd, ← hz]
  ext x
  have := hsep x
  simp only [hδ, AddMonoidHom.sub_apply, sub_eq_zero] at this
  exact this


-- created on 2026-10-24
