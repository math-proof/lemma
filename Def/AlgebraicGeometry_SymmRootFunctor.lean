module
public import Mathlib
public import Def.AlgebraicGeometry_RelativePicardFunctor
public import Theorem.Scheme.PolarisationRosati
public import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
public import Instance.AlgebraicGeometry_SymmRootFunctor
public import Structure.AlgebraicGeometry_SymmRootFunctor
public import Abbrev.AlgebraicGeometry_SymmRootFunctor
set_option autoImplicit false


public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra Scheme
  GoodReductionJacobian AlgebraicGeometry.Polarisation

namespace AlgebraicGeometry.SymmRoot

section base
variable (S : Type u) [CommRing S] (R₀ : Type u) [CommRing R₀] [Algebra S R₀]

abbrev ι (B : Under (CommRingCat.of R₀)) : Spec (CommRingCat.of B.right) ⟶ Spec (CommRingCat.of S) :=
  letI := algS S R₀ B
  Spec.map (CommRingCat.ofHom (algebraMap S B.right))

def ψ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') : SchemeHomOver (ι S R₀ B') (ι S R₀ B) :=
  ⟨Spec.map φ.right, by
    letI := algS S R₀ B; letI := algS S R₀ B'
    change Spec.map (CommRingCat.ofHom φ.right.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap S B.right)) =
      Spec.map (CommRingCat.ofHom (algebraMap S B'.right))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, comp_algebraMap]⟩

end base

section functor
variable {S : Type u} [CommRing S] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of S))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) c) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]


variable (P : StablePred c ε R₀)


def Elem.map {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (x : Elem c ε R₀ P B) : Elem c ε R₀ P B' :=
  ⟨x.M.pullbackAlong (ψ S R₀ φ), P.of_pullbackAlong φ x.M x.prop⟩

def classFunctor : Under (CommRingCat.of R₀) ⥤ Type (u + 1) where
  obj B := Quotient (setoid c ε R₀ P B)
  map {B B'} φ := TypeCat.ofHom
    (Quotient.map (Elem.map c ε R₀ P φ) (fun x y h => RigidifiedLineBundle.pullbackAlong_congr _ h))
  map_id B := TypeCat.homEquiv.injective (funext fun x => by
    induction x using Quotient.ind with
    | _ r =>
      exact Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_ψ_id c R₀ B)).app r.M.L ≪≫ (Scheme.Modules.pullbackId _).app r.M.L⟩)
  map_comp {B B' B''} φ χ := TypeCat.homEquiv.injective (funext fun x => by
    induction x using Quotient.ind with
    | _ r =>
      exact Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_ψ_comp c R₀ φ χ)).app r.M.L ≪≫
          ((Scheme.Modules.pullbackComp _ _).app r.M.L).symm⟩)

abbrev mk {B : Under (CommRingCat.of R₀)} (x : Elem c ε R₀ P B) : (classFunctor c ε R₀ P).obj B := Quotient.mk _ x

def truePred : StablePred c ε R₀ := ⟨fun _ _ => True, fun _ _ _ => trivial⟩

end functor

section symmRoot
variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (𝓛 : A.Modules) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]

def symmRootPred (B : Under (CommRingCat.of R₀)) (M : (pullback f (ι S R₀ B)).Modules) : Prop :=
  IsSymmetric (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)) M ∧
  LocIsoOnBase (pullback.snd f (ι S R₀ B))
    ((Scheme.Modules.pullback (pullback.fst f (ι S R₀ B))).obj 𝓛)
    (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)))).obj M)

abbrev symmRootStablePred
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (M : RigidifiedLineBundle f (L.one (𝟙 _)) (ι S R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (ψ S R₀ φ)).L) :
    StablePred f (L.one (𝟙 _)) R₀ :=
  ⟨symmRootPred L 𝓛 R₀, h⟩

end symmRoot

end AlgebraicGeometry.SymmRoot

end
