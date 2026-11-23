module

public import Mathlib
public import Def.AlgebraicGeometry_RelativePicardFunctor
public import Theorem.Scheme.PolarisationRosati
public import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
public import Instance.AlgebraicGeometry_SymmRootFunctor
public import Structure.AlgebraicGeometry_SymmRootFunctor
public import Abbrev.AlgebraicGeometry_SymmRootFunctor

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra Scheme
  GoodReductionJacobian AlgebraicGeometry.Polarisation

namespace AlgebraicGeometry.SymmRoot

section base
variable (S : Type u) [CommRing S] (R₀ : Type u) [CommRing R₀] [Algebra S R₀]


public theorem comp_algebraMap {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') :
    letI := algS S R₀ B; letI := algS S R₀ B'
    φ.right.hom.comp (algebraMap S B.right) = algebraMap S B'.right := by
  ext x
  change φ.right.hom (B.hom.hom (algebraMap S R₀ x)) = B'.hom.hom (algebraMap S R₀ x)
  rw [← Under.w φ]
  rfl


@[simp] public theorem ψ_val {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') : (ψ S R₀ φ).1 = Spec.map φ.right := rfl


public theorem ψ_id (B : Under (CommRingCat.of R₀)) : (ψ S R₀ (𝟙 B)).1 = 𝟙 _ := by
  rw [ψ_val]; exact Spec.map_id _


public theorem ψ_comp {B B' B'' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (χ : B' ⟶ B'') :
    (ψ S R₀ (φ ≫ χ)).1 = (ψ S R₀ χ).1 ≫ (ψ S R₀ φ).1 := by
  simp only [ψ_val, Under.comp_right, Spec.map_comp]

end base

section functor
variable {S : Type u} [CommRing S] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of S))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) c) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]


variable (P : StablePred c ε R₀)


@[simp] public theorem Elem.map_M {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (x : Elem c ε R₀ P B) :
    (x.map c ε R₀ P φ).M = x.M.pullbackAlong (ψ S R₀ φ) := rfl


public theorem baseChangeSnd_ψ_id (B : Under (CommRingCat.of R₀)) : baseChangeSnd c (ψ S R₀ (𝟙 B)) = 𝟙 _ := by
  rw [← baseChangeSnd_id c (ι S R₀ B)]
  unfold baseChangeSnd
  congr 1
  exact ψ_id S R₀ B


public theorem baseChangeSnd_ψ_comp {B B' B'' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (χ : B' ⟶ B'') :
    baseChangeSnd c (ψ S R₀ (φ ≫ χ)) = baseChangeSnd c (ψ S R₀ χ) ≫ baseChangeSnd c (ψ S R₀ φ) := by
  rw [baseChangeSnd_comp]
  congr 1
  exact Subtype.ext (ψ_comp S R₀ φ χ)


public theorem mk_surjective (B : Under (CommRingCat.of R₀)) : Function.Surjective (mk c ε R₀ P (B := B)) :=
  Quotient.mk_surjective


public theorem mk_eq_mk_iff {B : Under (CommRingCat.of R₀)} (x y : Elem c ε R₀ P B) :
    mk c ε R₀ P x = mk c ε R₀ P y ↔ Nonempty (x.M.L ≅ y.M.L) :=
  Quotient.eq


@[simp] public theorem map_mk {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (x : Elem c ε R₀ P B) :
    (classFunctor c ε R₀ P).map φ (mk c ε R₀ P x) = mk c ε R₀ P (x.map c ε R₀ P φ) := rfl


@[simp] public theorem classFunctor_obj (B : Under (CommRingCat.of R₀)) :
    (classFunctor c ε R₀ P).obj B = Quotient (setoid c ε R₀ P B) := rfl

example (B : Under (CommRingCat.of R₀)) (x : (classFunctor c ε R₀ P).obj B) :
    (classFunctor c ε R₀ P).map (𝟙 B) x = x := by
  rw [(classFunctor c ε R₀ P).map_id]; rfl


public theorem symmRootPred_iff (B : Under (CommRingCat.of R₀)) (M : (pullback f (ι S R₀ B)).Modules) :
    symmRootPred L 𝓛 R₀ B M ↔
      IsSymmetric (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)) M ∧
      LocIsoOnBase (pullback.snd f (ι S R₀ B))
        ((Scheme.Modules.pullback (pullback.fst f (ι S R₀ B))).obj 𝓛)
        (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)))).obj M) :=
  Iff.rfl

