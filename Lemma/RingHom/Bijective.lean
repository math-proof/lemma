import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_ringEquiv_noetherian_typeFamily](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_ringEquiv_noetherian_typeFamily.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {O : Type} [CommRing O]
  {B C : Type} [CommRing B] [CommRing C] [IsNoetherianRing B] [IsNoetherianRing C]
  {Gobj : ∀ (B : Type) [CommRing B] (_ : O →+* B), IsNilpotent (p : B) → Type u}
  {Gmap : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'} (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'), f.comp ψ = ψ' → Gobj B ψ hB → Gobj B' ψ' hB'}
  {Hobj : ∀ (B : Type) [CommRing B] (_ : O →+* B), IsNilpotent (p : B) → Type v}
  {Hmap : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'} (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'), f.comp ψ = ψ' → Hobj B ψ hB → Hobj B' ψ' hB'}
  {ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), Gobj B ψ hB → Hobj B ψ hB}
  {ψ : O →+* B}
  {e : B ≃+* C}
  -- given
  (Gmap_id : ∀ {B : Type} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : Gobj B ψ hB), Gmap hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x)
  (Gmap_comp : ∀ {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''} (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B'')) (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : Gobj B ψ hB), Gmap hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x = Gmap hB' hB'' g hg (Gmap hB hB' f hf x))
  (Hmap_id : ∀ {B : Type} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : Hobj B ψ hB), Hmap hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x)
  (Hmap_comp : ∀ {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''} (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B'')) (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : Hobj B ψ hB), Hmap hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x = Hmap hB' hB'' g hg (Hmap hB hB' f hf x))
  (hξ : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ') (x : Gobj B ψ hB), ξ B' ψ' hB' (Gmap hB hB' f hf x) = Hmap hB hB' f hf (ξ B ψ hB x))
  (hB : IsNilpotent (p : B))
  (hC : IsNilpotent (p : C))
  (h : Function.Bijective (ξ C (e.toRingHom.comp ψ) hC)) :
  -- imply
  Function.Bijective (ξ B ψ hB) := by
  -- proof
  classical
  have hf : e.toRingHom.comp ψ = e.toRingHom.comp ψ := rfl
  have hg : e.symm.toRingHom.comp (e.toRingHom.comp ψ) = ψ := by
    ext x
    simp
  have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id B := by
    ext x
    simp
  have idG : ∀ (g : B →+* B) (hg' : g.comp ψ = ψ), g = RingHom.id B → ∀ x : Gobj B ψ hB, Gmap hB hB g hg' x = x := by
    intro g hg' hgid x
    subst hgid
    apply Gmap_id hB x
  have idH : ∀ (g : B →+* B) (hg' : g.comp ψ = ψ), g = RingHom.id B → ∀ y : Hobj B ψ hB, Hmap hB hB g hg' y = y := by
    intro g hg' hgid y
    subst hgid
    apply Hmap_id hB y
  have backG : ∀ x : Gobj B ψ hB, Gmap hC hB e.symm.toRingHom hg (Gmap hB hC e.toRingHom hf x) = x := by
    intro x
    rw [← Gmap_comp hB hC hB e.symm.toRingHom e.toRingHom hf hg x]
    apply idG _ _ hcomp x
  have backH : ∀ y : Hobj B ψ hB, Hmap hC hB e.symm.toRingHom hg (Hmap hB hC e.toRingHom hf y) = y := by
    intro y
    rw [← Hmap_comp hB hC hB e.symm.toRingHom e.toRingHom hf hg y]
    apply idH _ _ hcomp y
  constructor
  ·
    intro x x' hxx
    have h1 := congrArg (Hmap hB hC e.toRingHom hf) hxx
    rw [← hξ B C ψ _ hB hC e.toRingHom hf x, ← hξ B C ψ _ hB hC e.toRingHom hf x'] at h1
    have h2 := h.1 h1
    have h3 := congrArg (Gmap hC hB e.symm.toRingHom hg) h2
    rwa [backG, backG] at h3
  ·
    intro y
    obtain ⟨x', hx'⟩ := h.2 (Hmap hB hC e.toRingHom hf y)
    refine ⟨Gmap hC hB e.symm.toRingHom hg x', ?_⟩
    rw [hξ C B _ ψ hC hB e.symm.toRingHom hg x', hx', backH]


-- created on 2026-10-20
