import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma piece
  (p : ℕ) [Fact p.Prime]
  {X Y : (Scheme : Type 1)}
  (fX : X ⟶ Spec (CommRingCat.of (ZMod p))) (fY : Y ⟶ Spec (CommRingCat.of (ZMod p)))
    (FX : X ⟶ X) (FY : Y ⟶ Y)
    (hFX : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X), x ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) → Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ FX)
    (hFY : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (y : Spec (CommRingCat.of B) ⟶ Y), y ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) → Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ y = y ≫ FY)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) {R : (CommRingCat : Type 1)} (ι : Spec R ⟶ X) :
    ι ≫ (FX ≫ g) = ι ≫ (g ≫ FY) := by
  let _ : Algebra (ZMod p) R := (Spec.preimage (ι ≫ fX)).hom.toAlgebra
  have hx : ι ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) R)) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  if hR : Nontrivial R then
    let _ : CharP R p := charP_of_injective_algebraMap (algebraMap (ZMod p) R).injective p
    have h1 := hFX R ι hx
    have h2 := hFY R (ι ≫ g) (by rw [Category.assoc, hg, hx])
    rw [← Category.assoc, ← h1, Category.assoc, h2, Category.assoc]
  else
    let _ : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    let _ : IsEmpty ↥(Spec R) := by
      show IsEmpty (PrimeSpectrum R)
      infer_instance
    apply (isInitialOfIsEmpty (X := Spec R)).hom_ext

private lemma helper_main
  (p : ℕ) [Fact p.Prime]
  {X Y : (Scheme : Type 1)}
  (fX : X ⟶ Spec (CommRingCat.of (ZMod p))) (fY : Y ⟶ Spec (CommRingCat.of (ZMod p)))
    (FX : X ⟶ X) (FY : Y ⟶ Y) (_ : FX ≫ fX = fX) (_ : FY ≫ fY = fY)
    (hFX : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X), x ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) → Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ FX)
    (hFY : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (y : Spec (CommRingCat.of B) ⟶ Y), y ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) → Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ y = y ≫ FY)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    FX ≫ g = g ≫ FY :=
  Scheme.Cover.hom_ext X.affineCover _ _ fun j => piece p fX fY FX FY hFX hFY g hg (X.affineCover.f j)

/--
[AlgebraicGeometry_frobenius_comp_eq_comp_frobenius_of_forall_spec](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_frobenius_comp_eq_comp_frobenius_of_forall_spec.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime]
  {X Y : (Scheme : Type 1)}
  (fX : X ⟶ Spec (CommRingCat.of (ZMod p))) (fY : Y ⟶ Spec (CommRingCat.of (ZMod p)))
    (FX : X ⟶ X) (FY : Y ⟶ Y) (hFXb : FX ≫ fX = fX) (hFYb : FY ≫ fY = fY)
    (hFX : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X), x ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) → Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ FX)
    (hFY : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (y : Spec (CommRingCat.of B) ⟶ Y), y ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) → Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ y = y ≫ FY)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    FX ≫ g = g ≫ FY :=
  helper_main p fX fY FX FY hFXb hFYb hFX hFY g hg


-- created on 2026-10-20
