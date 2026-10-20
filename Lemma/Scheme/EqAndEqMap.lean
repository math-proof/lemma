import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private noncomputable def powHom (p : ℕ) (hp : p.Prime) (R : Type*) [CommRing R] (h : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.ne_zero
  map_add' x y := by
    rw [add_pow_prime_eq hp, h]
    simp
private lemma powHom_apply (p : ℕ) (hp : p.Prime) (R : Type*) [CommRing R] (h : (p : R) = 0) (x : R) :
    powHom p hp R h x = x ^ p := rfl
private lemma comp_eq_comp_of_forall_eq_pow {p : ℕ} {A C : Type*} [CommRing A] [CommRing C]
    (u : A →+* A) (v : C →+* C) (hu : ∀ a, u a = a ^ p) (hv : ∀ c, v c = c ^ p) (θ : A →+* C) :
    θ.comp u = v.comp θ := by
  ext a
  simp [hu, hv, map_pow]
private lemma spec_comm {p : ℕ} {A C : CommRingCat.{0}} (u : A ⟶ A) (v : C ⟶ C)
    (hu : ∀ a, u.hom a = a ^ p) (hv : ∀ c, v.hom c = c ^ p) (θ : A ⟶ C) :
    Spec.map θ ≫ Spec.map u = Spec.map v ≫ Spec.map θ := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  simp [hu, hv, map_pow]
private lemma natCast_eq_zero_of_hom (p : ℕ) {A C : Type*} [CommRing A] [CommRing C] (θ : A →+* C) (h : (p : A) = 0) :
    (p : C) = 0 := by
  rw [← map_natCast θ p, h, map_zero]
private lemma point_comm (p : ℕ) (hp : p.Prime) {A C : CommRingCat.{0}} {X : Scheme.{0}} (u : A ⟶ A)
    (hu : ∀ a, u.hom a = a ^ p) (g : Spec A ⟶ X) (b : Spec C ⟶ Spec A) (hpC : (p : C) = 0) :
    b ≫ Spec.map u ≫ g = Spec.map (CommRingCat.ofHom (powHom p hp C hpC)) ≫ b ≫ g := by
  have hb : b = Spec.map (Spec.preimage b) := (Spec.map_preimage b).symm
  rw [hb, ← Category.assoc, spec_comm u (CommRingCat.ofHom (powHom p hp C hpC)) hu (fun _ => rfl) (Spec.preimage b),
    Category.assoc]
private lemma natCast_eq_zero_of_point (p : ℕ) {A C : CommRingCat.{0}} (b : Spec C ⟶ Spec A) (h : (p : A) = 0) :
    (p : C) = 0 :=
  natCast_eq_zero_of_hom p (Spec.preimage b).hom h
private lemma helper_main (p : ℕ) [hp : Fact p.Prime] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (ZMod p))) :
    ∃ F : X ⟶ X, F ≫ f = f ∧
      ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ F := by
  classical
  let 𝒰 := X.affineCover
  let R : 𝒰.I₀ → CommRingCat.{0} := fun j => (X.local_affine j).choose_spec.choose
  let ιj : ∀ j, Spec (R j) ⟶ X := fun j => 𝒰.f j
  have hιj : ∀ j, 𝒰.f j = ιj j := fun _ => rfl
  let ψ : ∀ j, CommRingCat.of (ZMod p) ⟶ R j := fun j => Spec.preimage (ιj j ≫ f)
  have hψ : ∀ j, Spec.map (ψ j) = ιj j ≫ f := fun j => Spec.map_preimage _
  have hpR : ∀ j, (p : R j) = 0 := fun j => natCast_eq_zero_of_hom p (ψ j).hom (ZMod.natCast_self p)
  let φ : ∀ j, R j ⟶ R j := fun j => CommRingCat.ofHom (powHom p hp.out (R j) (hpR j))
  have hφ : ∀ j (a : R j), (φ j).hom a = a ^ p := fun _ _ => rfl
  let Fj : ∀ j, Spec (R j) ⟶ X := fun j => Spec.map (φ j) ≫ ιj j
  have hFj : ∀ j, Fj j = Spec.map (φ j) ≫ ιj j := fun _ => rfl
  have hcompat' : ∀ i j, pullback.fst (ιj i) (ιj j) ≫ Fj i = pullback.snd (ιj i) (ιj j) ≫ Fj j := by
    intro i j
    have key : ∀ {C : CommRingCat.{0}} (ι : Spec C ⟶ pullback (ιj i) (ιj j)),
        ι ≫ pullback.fst (ιj i) (ιj j) ≫ Fj i = ι ≫ pullback.snd (ιj i) (ιj j) ≫ Fj j := by
      intro C ι
      have hpC : (p : C) = 0 := natCast_eq_zero_of_point p (ι ≫ pullback.fst (ιj i) (ιj j)) (hpR i)
      have e1 := point_comm p hp.out (φ i) (hφ i) (ιj i) (ι ≫ pullback.fst (ιj i) (ιj j)) hpC
      have e2 := point_comm p hp.out (φ j) (hφ j) (ιj j) (ι ≫ pullback.snd (ιj i) (ιj j)) hpC
      calc ι ≫ pullback.fst (ιj i) (ιj j) ≫ Fj i
          = (ι ≫ pullback.fst (ιj i) (ιj j)) ≫ Spec.map (φ i) ≫ ιj i := by rw [hFj, Category.assoc]
        _ = _ := e1
        _ = Spec.map (CommRingCat.ofHom (powHom p hp.out C hpC)) ≫ (ι ≫ pullback.snd (ιj i) (ιj j)) ≫ ιj j := by
            simp only [Category.assoc, pullback.condition]
        _ = (ι ≫ pullback.snd (ιj i) (ιj j)) ≫ Spec.map (φ j) ≫ ιj j := e2.symm
        _ = ι ≫ pullback.snd (ιj i) (ιj j) ≫ Fj j := by rw [hFj, Category.assoc]
    exact Scheme.Cover.hom_ext (pullback (ιj i) (ιj j)).affineCover _ _ fun k =>
      key ((pullback (ιj i) (ιj j)).affineCover.f k)
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ Fj i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ Fj j :=
    hcompat'
  let F : X ⟶ X := Scheme.Cover.glueMorphisms 𝒰 Fj hcompat
  have hF : ∀ j, ιj j ≫ F = Fj j := Scheme.Cover.ι_glueMorphisms 𝒰 Fj hcompat
  refine ⟨F, ?_, ?_⟩
  ·
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun j => ?_
    change ιj j ≫ F ≫ f = ιj j ≫ f
    have hfix : Spec.map (φ j) ≫ Spec.map (ψ j) = Spec.map (ψ j) := by
      rw [← Spec.map_comp]
      congr 1
      ext a
      change (φ j).hom ((ψ j).hom a) = (ψ j).hom a
      rw [hφ, ← map_pow, ZMod.pow_card]
    calc ιj j ≫ F ≫ f = Fj j ≫ f := by rw [← Category.assoc, hF]
      _ = Spec.map (φ j) ≫ (ιj j ≫ f) := by rw [hFj, Category.assoc]
      _ = Spec.map (φ j) ≫ Spec.map (ψ j) := by rw [hψ]
      _ = Spec.map (ψ j) := hfix
      _ = ιj j ≫ f := hψ j
  ·
    intro B _ _ _ x hx
    have hpB : (p : (CommRingCat.of B)) = 0 := CharP.cast_eq_zero B p
    have key : ∀ (j : 𝒰.I₀) {C : CommRingCat.{0}} (ι : Spec C ⟶ pullback x (ιj j)),
        ι ≫ pullback.fst x (ιj j) ≫ (Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x) =
          ι ≫ pullback.fst x (ιj j) ≫ (x ≫ F) := by
      intro j C ι
      have hpC : (p : C) = 0 := natCast_eq_zero_of_point p (ι ≫ pullback.fst x (ιj j)) hpB
      have e1 := point_comm p hp.out (CommRingCat.ofHom (frobenius B p)) (fun b => frobenius_def p b) x
        (ι ≫ pullback.fst x (ιj j)) hpC
      have e2 := point_comm p hp.out (φ j) (hφ j) (ιj j) (ι ≫ pullback.snd x (ιj j)) hpC
      calc ι ≫ pullback.fst x (ιj j) ≫ (Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x)
          = (ι ≫ pullback.fst x (ιj j)) ≫ Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x := by
            simp only [Category.assoc]
        _ = _ := e1
        _ = Spec.map (CommRingCat.ofHom (powHom p hp.out C hpC)) ≫ (ι ≫ pullback.snd x (ιj j)) ≫ ιj j := by
            simp only [Category.assoc, pullback.condition]
        _ = (ι ≫ pullback.snd x (ιj j)) ≫ Spec.map (φ j) ≫ ιj j := e2.symm
        _ = (ι ≫ pullback.snd x (ιj j)) ≫ (ιj j ≫ F) := by rw [hF, hFj]
        _ = ι ≫ pullback.fst x (ιj j) ≫ (x ≫ F) := by
            simp only [Category.assoc]
            rw [pullback.condition_assoc]
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ x) _ _ fun j => ?_
    change pullback.fst x (ιj j) ≫ _ = pullback.fst x (ιj j) ≫ _
    exact Scheme.Cover.hom_ext (pullback x (ιj j)).affineCover _ _ fun k =>
      by have h__af := key j ((pullback x (ιj j)).affineCover.f k); simp only [Category.assoc] at h__af; exact h__af
/--
[AlgebraicGeometry_exists_frobenius_over_zmodp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_frobenius_over_zmodp.lean)
-/
@[path]
private lemma main
    (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (ZMod p))) :
    ∃ F : X ⟶ X, F ≫ f = f ∧
      ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ F :=
  helper_main p f

-- created on 2026-10-20
