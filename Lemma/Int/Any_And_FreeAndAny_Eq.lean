import Mathlib
import Initialize.Tactic.Attr.Basic
open Algebra.TensorProduct
open scoped TensorProduct


private lemma bijective_comp_includeLeft_includeRight
  {A : Type u} [CommRing A]
  {H₁ : Type u} [CommRing H₁] [Algebra A H₁]
  {H₂ : Type u} [CommRing H₂] [Algebra A H₂]
  {T : Type u} [CommRing T] [Algebra A T] :
-- imply
  Function.Bijective (fun f : H₁ ⊗[A] H₂ →ₐ[A] T => (f.comp includeLeft, f.comp includeRight)) := by
-- proof
  constructor
  ·
    intro f g h
    simp only [Prod.mk.injEq] at h
    apply Algebra.TensorProduct.ext'
    intro a b
    have h1 := congrArg (fun φ : H₁ →ₐ[A] T => φ a) h.1
    have h2 := congrArg (fun φ : H₂ →ₐ[A] T => φ b) h.2
    simp only [AlgHom.coe_comp, Function.comp_apply, includeLeft_apply, includeRight_apply] at h1 h2
    rw [show a ⊗ₜ[A] b = (a ⊗ₜ[A] (1 : H₂)) * ((1 : H₁) ⊗ₜ[A] b) by simp, map_mul, map_mul, h1, h2]
  ·
    rintro ⟨f₁, f₂⟩
    refine ⟨Algebra.TensorProduct.lift f₁ f₂ fun _ _ => .all _ _, ?_⟩
    simp [lift_comp_includeLeft, lift_comp_includeRight']


/--
[Algebra_exists_algHom_equiv_pi](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_algHom_equiv_pi.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A]
  {ι : Type} [Finite ι]
  {H : ι → Type u} [∀ i, CommRing (H i)] [∀ i, Algebra A (H i)] [∀ i, Module.Finite A (H i)] [∀ i, Module.Free A (H i)] :
-- imply
  ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W),
    Module.Finite A W ∧ Module.Free A W ∧
    ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (∀ i, H i →ₐ[A] T),
      ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T') (f : W →ₐ[A] T),
        e T' (u.comp f) = fun i => u.comp (e T f i) := by
-- proof
  induction ι using Finite.induction_empty_option with
  | of_equiv eqv ih =>
    rename_i α β _
    obtain ⟨W, i1, i2, hfin, hfree, e, hnat⟩ := @ih (fun a => H (eqv a)) (fun a => inferInstance)
      (fun a => inferInstance) (fun a => inferInstance) (fun a => inferInstance)
    refine ⟨W, i1, i2, hfin, hfree, fun T _ _ => (e T).trans (Equiv.piCongrLeft (fun b => H b →ₐ[A] T) eqv), ?_⟩
    intro T T' _ _ _ _ u f
    funext b
    obtain ⟨a, rfl⟩ := eqv.surjective b
    simp only [Equiv.trans_apply]
    rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply, hnat]
  | h_empty =>
    refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, fun T _ _ => ⟨fun _ i => PEmpty.elim i, fun _ => Algebra.ofId A T, fun f => Subsingleton.elim _ _, fun g => funext fun i => PEmpty.elim i⟩, ?_⟩
    intro T T' _ _ _ _ u f
    funext i
    apply PEmpty.elim i
  | h_option ih =>
    rename_i α _
    obtain ⟨W₀, i1, i2, hfin, hfree, e₀, hnat₀⟩ := @ih (fun a => H (some a)) (fun a => inferInstance)
      (fun a => inferInstance) (fun a => inferInstance) (fun a => inferInstance)
    let _ : Module.Finite A W₀ := hfin
    let _ : Module.Free A W₀ := hfree
    refine ⟨W₀ ⊗[A] H none, inferInstance, inferInstance, inferInstance, inferInstance, fun T _ _ => (Equiv.ofBijective _ (bijective_comp_includeLeft_includeRight (H₁ := W₀) (H₂ := H none) (T := T))).trans (((e₀ T).prodCongr (Equiv.refl _)).trans ((Equiv.prodComm _ _).trans (Equiv.piOptionEquivProd (β := fun o => H o →ₐ[A] T)).symm)), ?_⟩
    intro T T' _ _ _ _ u f
    funext o
    cases o with
    | none =>
      rfl
    | some a =>
      simp only [Equiv.trans_apply, Equiv.ofBijective_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, Equiv.prodComm_apply, Prod.swap, Equiv.piOptionEquivProd, Equiv.coe_fn_symm_mk]
      apply congrFun (hnat₀ T T' u (f.comp includeLeft)) a


-- created on 2026-10-13
