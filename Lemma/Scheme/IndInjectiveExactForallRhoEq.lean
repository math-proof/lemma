import Mathlib
import sympy.Basic
open CategoryTheory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma unit_apply_coe {k : Type u} [CommRing k] {G : Type v} [Group G] (N : Subgroup G) (B : Rep k G) (b : B) (g : G) : (((Rep.resCoindAdjunction k N.subtype).unit.app B).hom b).1 g = B.ρ g b := rfl
private lemma unit_injective {k : Type u} [CommRing k] {G : Type v} [Group G] (N : Subgroup G) (B : Rep k G) : Function.Injective ((Rep.resCoindAdjunction k N.subtype).unit.app B).hom := by
  intro b b' h
  have h1 : B.ρ 1 b = B.ρ 1 b' := congrArg (fun f : Rep.coind N.subtype (Rep.res N.subtype B) => f.1 1) h
  rwa [map_one, Module.End.one_apply, Module.End.one_apply] at h1
private lemma coind_ρ_eq_self {k : Type u} [CommRing k] {G : Type v} [Group G] (N : Subgroup G) [hNn : N.Normal] (B : Rep k G) (hN : ∀ g ∈ N, ∀ b : B, B.ρ g b = b) (n : G) (hn : n ∈ N) (f : Rep.coind N.subtype (Rep.res N.subtype B)) : (Rep.coind N.subtype (Rep.res N.subtype B)).ρ n f = f := by
  apply Subtype.ext
  funext g
  change f.1 (g * n) = f.1 g
  have hmem : g * n * g⁻¹ ∈ N := hNn.conj_mem n hn g
  have h := f.2 ⟨g * n * g⁻¹, hmem⟩ g
  change f.1 (g * n * g⁻¹ * g) = B.ρ (g * n * g⁻¹) (f.1 g) at h
  rw [inv_mul_cancel_right] at h
  rw [h, hN _ hmem]
private lemma iso_hom_injective {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep k G} (e : X ≅ Y) : Function.Injective e.hom.hom := by
  intro x y h
  have := congrArg e.inv.hom h
  change (e.hom ≫ e.inv).hom x = (e.hom ≫ e.inv).hom y at this
  rwa [e.hom_inv_id] at this
private lemma iso_inv_injective {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep k G} (e : X ≅ Y) : Function.Injective e.inv.hom := iso_hom_injective e.symm
private def homAdd {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep k G} (a : X ⟶ Y) : X →+ Y := a.hom.toLinearMap.toAddMonoidHom
private lemma homAdd_apply {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep k G} (a : X ⟶ Y) (x : X) : homAdd a x = a.hom x := rfl
private lemma nsmul_coind_eq_zero {k : Type u} [CommRing k] {G : Type v} [Group G] (N : Subgroup G) (B : Rep k G) (p : ℕ) (hB : ∀ b : B, p • b = 0) (f : Rep.coind N.subtype (Rep.res N.subtype B)) : p • f = 0 := by
  apply Subtype.ext
  funext g
  change p • f.1 g = 0
  apply hB _
private noncomputable abbrev cokerObj {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep k G} (f : X ⟶ Y) : Rep k G :=
  Rep.of (Representation.quotient Y.ρ (LinearMap.range f.hom.toLinearMap) fun g => by
    rintro _ ⟨a, rfl⟩
    exact ⟨X.ρ g a, Rep.hom_comm_apply f g a⟩)
private noncomputable def cokerπ {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep k G} (f : X ⟶ Y) : Y ⟶ cokerObj f := Rep.ofHom ⟨Submodule.mkQ _, fun _ => rfl⟩
private lemma cokerπ_hom_apply {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep k G} (f : X ⟶ Y) (y : Y) : (cokerπ f).hom y = Submodule.Quotient.mk y := rfl
private lemma cokerπ_hom_surjective {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep k G} (f : X ⟶ Y) : Function.Surjective (cokerπ f).hom := Submodule.mkQ_surjective _
private lemma cokerπ_hom_apply_eq_zero_iff {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep k G} (f : X ⟶ Y) (y : Y) : (cokerπ f).hom y = 0 ↔ y ∈ LinearMap.range f.hom.toLinearMap := by
  rw [cokerπ_hom_apply, Submodule.Quotient.mk_eq_zero]
/--
[Rep_exists_hom_ind_injective_exact_of_forall_rho_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_exists_hom_ind_injective_exact_of_forall_rho_eq.lean)
-/
@[path]
private lemma main
  {G : Type} [Group G] [Fintype G]
  (N : Subgroup G) [N.Normal]
  (B : Rep ℤ G) [Fintype B]
  (p : ℕ)
  -- given
  (hB : ∀ b : B, p • b = 0)
  (hN : ∀ g ∈ N, ∀ b : B, B.ρ g b = b) :
  -- imply
  ∃ (ι : B ⟶ (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B)) (B₁ : Rep ℤ G) (_ : Fintype B₁) (ρ : (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B) ⟶ B₁), Function.Injective ι.hom ∧ Function.Exact ι.hom ρ.hom ∧ Function.Surjective ρ.hom ∧ (∀ b : B₁, p • b = 0) ∧ (∀ g ∈ N, ∀ b : B₁, B₁.ρ g b = b) ∧ (∀ g ∈ N, ∀ x : (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B), ((Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B)).ρ g x = x) := by
  -- proof
  classical
  let _ : N.FiniteIndex := inferInstance
  let A : Rep ℤ ↥N := Rep.res N.subtype B
  let e : Rep.ind N.subtype A ≅ Rep.coind N.subtype A := Rep.indCoindIso A
  let η : B ⟶ Rep.coind N.subtype A := (Rep.resCoindAdjunction ℤ N.subtype).unit.app B
  let ι : B ⟶ (Rep.indFunctor ℤ N.subtype).obj A := η ≫ e.inv
  have hιinj : Function.Injective ι.hom := fun b b' h => unit_injective N B (iso_inv_injective e h)
  have hNind : ∀ g ∈ N, ∀ x : (Rep.indFunctor ℤ N.subtype).obj A, ((Rep.indFunctor ℤ N.subtype).obj A).ρ g x = x := by
    intro g hg x
    apply iso_hom_injective e
    apply (Rep.hom_comm_apply e.hom g x).trans (coind_ρ_eq_self N B hN g hg (e.hom.hom x))
  let B₁ : Rep ℤ G := cokerObj ι
  let ρ₁ : (Rep.indFunctor ℤ N.subtype).obj A ⟶ B₁ := cokerπ ι
  have hsurj : Function.Surjective ρ₁.hom := cokerπ_hom_surjective ι
  have hexact : Function.Exact ι.hom ρ₁.hom := by
    intro y
    rw [cokerπ_hom_apply_eq_zero_iff]
    constructor
    ·
      rintro ⟨x, hx⟩
      exact ⟨x, hx⟩
    ·
      rintro ⟨x, hx⟩
      exact ⟨x, hx⟩
  let _ : Finite (Rep.coind N.subtype A) := Finite.of_injective (fun f : Rep.coind N.subtype A => f.1) Subtype.val_injective
  let _ : Finite ((Rep.indFunctor ℤ N.subtype).obj A) := Finite.of_injective _ (iso_hom_injective e)
  let _ : Finite B₁ := Finite.of_surjective _ hsurj
  refine ⟨ι, B₁, Fintype.ofFinite B₁, ρ₁, hιinj, hexact, hsurj, ?_, ?_, hNind⟩
  ·
    intro b
    obtain ⟨x, rfl⟩ := hsurj b
    change p • homAdd ρ₁ x = 0
    rw [← map_nsmul]
    have hx : p • x = 0 := by
      apply iso_hom_injective e
      have h1 : e.hom.hom (p • x) = p • e.hom.hom x := map_nsmul (homAdd e.hom) p x
      rw [h1, nsmul_coind_eq_zero N B p hB]
      apply (map_zero (homAdd e.hom)).symm
    rw [hx, map_zero]
  ·
    intro g hg b
    obtain ⟨x, rfl⟩ := hsurj b
    rw [← Rep.hom_comm_apply, hNind g hg]


-- created on 2026-10-20
